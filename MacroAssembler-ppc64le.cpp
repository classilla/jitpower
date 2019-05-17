/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jit/ppc64le/MacroAssembler-ppc64le.h"

#include "mozilla/DebugOnly.h"
#include "mozilla/MathAlgorithms.h"

#include "jit/Bailouts.h"
#include "jit/BaselineFrame.h"
#include "jit/JitFrames.h"
#include "jit/MacroAssembler.h"
#include "jit/MoveEmitter.h"
#include "jit/SharedICRegisters.h"

#include "jit/MacroAssembler-inl.h"

using namespace js;
using namespace jit;

using mozilla::Abs;

#if DEBUG

/* Useful class to print visual guard blocks. */
class AutoDeBlock
{
    private:
        const char *blockname;

    public:
        AutoDeBlock(const char *name) {
            blockname = name;
            JitSpew(JitSpew_Codegen, "[[ CGPPC: %s", blockname);
        }

        ~AutoDeBlock() {
            JitSpew(JitSpew_Codegen, "   CGPPC: %s ]]", blockname);
        }
};
#define ADBlock()  AutoDeBlock _adbx(__PRETTY_FUNCTION__)
#else

/* Useful macro to completely elide visual guard blocks. */
#define ADBlock()  ;

#endif

static_assert(sizeof(intptr_t) == 8, "Not 64-bit clean.");

void
MacroAssemblerPPC64LECompat::convertBoolToInt32(Register src, Register dest)
{
    ADBlock();
    // Note that C++ bool is only 1 byte, so zero extend it to clear the
    // higher-order bits.
    ma_and(dest, src, Imm32(0xff));
}

void
MacroAssemblerPPC64LECompat::convertInt32ToDouble(Register src, FloatRegister dest)
{
    // Power has no GPR<->FPR moves, and we may not have a linkage area,
    // so we do this on the stack (see also OPPCC chapter 8 p.156 for the
    // basic notion, but we have a better choice on POWER9 since we no
    // longer have to faff around with fake constants like we did in 32-bit).
    ADBlock();
    MOZ_ASSERT(dest != ScratchFloatReg);

    // Treat src as a 64-bit register (since it is) and spill to stack.
    as_stdu(src, StackPointer, -8);
    // Keep stdu and lfd in separate dispatch groups.
    as_nop();
    as_nop();
    as_nop();

    as_lfd(ScratchFloatReg, StackPointer, 0);
    as_fcfid(dest, ScratchFloatReg); // easy!
}

void
MacroAssemblerPPC64LECompat::convertUInt64ToDouble(Register src, FloatRegister dest)
{
    // Approximately the same as above, but using fcfidu.
    ADBlock();
    MOZ_ASSERT(dest != ScratchFloatReg);

    as_stdu(src, StackPointer, -8);
    // Keep stdu and lfd in separate dispatch groups.
    as_nop();
    as_nop();
    as_nop();

    as_lfd(ScratchFloatReg, StackPointer, 0);
    as_fcfidu(dest, ScratchFloatReg);
}

void
MacroAssemblerPPC64LECompat::convertInt32ToDouble(const Address& src, FloatRegister dest)
{
    ADBlock();
    load32(src, SecondScratchReg);
    convertInt32ToDouble(SecondScratchReg, dest);
}

void
MacroAssemblerPPC64LECompat::convertInt32ToDouble(const BaseIndex& src, FloatRegister dest)
{
    ADBlock();
    computeScaledAddress(src, ScratchRegister);
    convertInt32ToDouble(Address(ScratchRegister, src.offset), dest);
}

void
MacroAssemblerPPC64LECompat::convertUInt32ToDouble(Register src, FloatRegister dest)
{
    ADBlock();
    ma_dext(ScratchRegister, src, Imm32(0), Imm32(32));
    asMasm().convertUInt64ToDouble(Register64(ScratchRegister), dest);
}


void
MacroAssemblerPPC64LECompat::convertUInt32ToFloat32(Register src, FloatRegister dest)
{
    ADBlock();
    ma_dext(ScratchRegister, src, Imm32(0), Imm32(32));
    asMasm().convertUInt64ToFloat32(Register64(ScratchRegister), dest);
}

void
MacroAssemblerPPC64LECompat::convertDoubleToFloat32(FloatRegister src, FloatRegister dest)
{
    ADBlock();
    as_frsp(dest, src);
}

// Checks whether a double is representable as a 32-bit integer. If so, the
// integer is written to the output register. Otherwise, a bailout is taken to
// the given snapshot. This function overwrites the scratch float register.
void
MacroAssemblerPPC64LECompat::convertDoubleToInt32(FloatRegister src, Register dest,
                                                 Label* fail, bool negativeZeroCheck)
{
    ADBlock();
    MOZ_ASSERT(src != ScratchFloatReg);

    // fctiwz. will set an exception to CR1 if conversion is inexact
    // or invalid. We don't need to know the exact exception, just that
    // it went boom, so no need to check the FPSCR.
    as_fctiwz_rc(ScratchFloatReg, src);
    ma_bc(cr1, Assembler::LessThan, fail);

    // Spill to memory and pick up the value.
    as_stfdu(ScratchFloatReg, StackPointer, -8);
    as_nop();
    as_nop();
    as_nop();
    // Pull out the lower 32 bits. ENDIAN!!!
    as_lwz(dest, StackPointer, 0); // 4 for BE

    if (negativeZeroCheck) {
        // If we need to check negative 0, then dump the FPR on the stack
        // and look at the sign bit. fctiwz. will merrily convert -0 with
        // no exception because, well, it's zero!
        // The MIPS version happily clobbers dest from the beginning, so
        // no worries doing this check here to save some work.

        Label done;
        MOZ_ASSERT(dest != ScratchRegister && dest != SecondScratchReg);
        // Don't bother if the result was not zero.
        as_cmpldi(dest, 0);
        ma_bc(Assembler::NotEqual, &done, ShortJump);

        // Damn, the result was zero.
        // Dump the original float and check the two 32-bit halves.
        // 0x8000000 00000000 = -0.0
        // 0x0000000 00000000 = 0.0
        // Thus, if they're not the same, negative zero; bailout.
        as_stfd(src, StackPointer, 0); // reuse existing allocation
        as_nop();
        as_nop();
        as_nop(); // no sleepovers without supervision
        as_lwz(ScratchRegister, StackPointer, 0);
        as_lwz(SecondScratchReg, StackPointer, 4);
        as_cmplw(ScratchRegister, SecondScratchReg);
        as_addi(StackPointer, StackPointer, 8);
        ma_bc(Assembler::NotEqual, fail);

        bind(&done);
    } else {
        as_addi(StackPointer, StackPointer, 8);
    }
}

// Checks whether a float32 is representable as a 32-bit integer.
void
MacroAssemblerPPC64LECompat::convertFloat32ToInt32(FloatRegister src, Register dest,
                                                  Label* fail, bool negativeZeroCheck)
{
    // Since 32-bit and 64-bit FPRs are the same registers, use the same
    // routine above.
    ADBlock();
    convertDoubleToInt32(src, dest, fail, negativeZeroCheck);
}

void
MacroAssemblerPPC64LECompat::convertFloat32ToDouble(FloatRegister src, FloatRegister dest)
{
    // Nothing to do.
}

void
MacroAssemblerPPC64LECompat::convertInt32ToFloat32(Register src, FloatRegister dest)
{
    ADBlock();
    convertInt32ToDouble(src, dest);
    as_frsp(dest, dest); // probably overkill
}

void
MacroAssemblerPPC64LECompat::convertInt32ToFloat32(const Address& src, FloatRegister dest)
{
    ADBlock();
    ma_ls(ScratchRegister, src);
    convertInt32ToFloat32(ScratchRegister, dest);
}

void
MacroAssemblerPPC64LECompat::movq(Register rs, Register rd)
{
    ADBlock();
    ma_move(rd, rs);
}

void
MacroAssemblerPPC64LE::ma_li(Register dest, CodeLabel* label)
{
    ADBlock();
    BufferOffset bo = m_buffer.nextOffset();
    ma_liPatchable(dest, ImmWord(/* placeholder */ 0));
    label->patchAt()->bind(bo.getOffset());
    label->setLinkMode(CodeLabel::MoveImmediate);
}

// Generate an optimized sequence to load a 64-bit immediate.
void
MacroAssemblerPPC64LE::ma_li(Register dest, int64_t value)
{
    ADBlock();
    uint64_t bits = (uint64_t)value;
    bool loweronly = true;

    // Handle trivial 16-bit quantities.
    if (value > -32769 && value < 32768) {
        // fits in 16 low bits
        xs_li(dest, value); // mscdfr0 asserts
        return;
    }
    if ((bits & 0xffffffff0000ffff) == 0 ||
            (bits & 0xffffffff0000ffff) == 0xffffffff00000000) {
        // fits in 16 high bits
        xs_lis(dest, value >> 16); // mscdfr0 asserts
        return;
    }

    // Emit optimized sequence based on occupied bits.
    if (bits & 0xffff000000000000) {
        // Need to set upper word and shift.
        xs_lis(dest, bits >> 48);
        if (bits & 0x0000ffff00000000) {
            as_ori(dest, dest, (bits >> 32) & 0xffff);
        }
        as_rldicr(dest, dest, 32, 31);
        loweronly = false;
    } else if (bits & 0x0000ffff00000000) {
        xs_li(dest, (bits >> 32) & 0xffff);
        as_rldicr(dest, dest, 32, 31);
        loweronly = false;
    }

    // Now the lower word. Don't clobber the upper word!
    bits &= 0x00000000ffffffff;
    if (bits & 0xffff0000) {
        if (loweronly) {
            xs_lis(dest, bits >> 16);
        } else {
            as_oris(dest, dest, bits >> 16);
        }
        if (bits & 0x0000ffff) {
            as_ori(dest, dest, bits & 0xffff);
        }
    } else if (bits & 0x0000ffff) {
        if (loweronly) {
            xs_li(dest, bits & 0xffff);
        } else {
            as_ori(dest, dest, bits & 0xffff);
        }
    }
}
void
MacroAssemblerPPC64LE::ma_li(Register dest, ImmWord imm)
{
    ma_li(dest, imm.value);
}

// This generates immediate loads as well, but always in the
// long form so that they can be patched.
void
MacroAssemblerPPC64LE::ma_liPatchable(Register dest, ImmPtr imm)
{
    ma_liPatchable(dest, ImmWord(uintptr_t(imm.value)));
}

void
MacroAssemblerPPC64LE::ma_liPatchable(Register dest, ImmWord imm, LiFlags flags)
{
    ADBlock();
    if (Li64 == flags) {
        // 64-bit load.
        m_buffer.ensureSpace(5 * sizeof(uint32_t));
        xs_lis(dest, Imm16::Upper(Imm32(imm.value >> 32)).encode());
        as_ori(dest, dest, Imm16::Lower(Imm32(imm.value >> 32)).encode());
        as_rldicr(dest, dest, 32, 31);
        as_oris(dest, dest, Imm16::Upper(Imm32(imm.value)).encode());
        as_ori(dest, dest, Imm16::Lower(Imm32(imm.value)).encode());
    } else {
        // 48-bit load. XXX: Do we need this too?
        m_buffer.ensureSpace(4 * sizeof(uint32_t));
        xs_lis(dest, Imm16::Lower(Imm32(imm.value >> 32)).encode());
        as_ori(dest, dest, Imm16::Upper(Imm32(imm.value)).encode());
        as_rldicr(dest, dest, 16, 47);
        as_ori(dest, dest, Imm16::Lower(Imm32(imm.value)).encode());
    }
}

void
MacroAssemblerPPC64LE::ma_dnegu(Register rd, Register rs)
{
    ADBlock();
    as_neg(rd, rs);
}

// Shifts
void
MacroAssemblerPPC64LE::ma_dsll(Register rd, Register rt, Imm32 shift)
{
    if (31 < shift.value)
      as_dsll32(rd, rt, shift.value);
    else
      as_dsll(rd, rt, shift.value);
}

void
MacroAssemblerPPC64LE::ma_dsrl(Register rd, Register rt, Imm32 shift)
{
    if (31 < shift.value)
      as_dsrl32(rd, rt, shift.value);
    else
      as_dsrl(rd, rt, shift.value);
}

void
MacroAssemblerPPC64LE::ma_dsra(Register rd, Register rt, Imm32 shift)
{
    if (31 < shift.value)
      as_dsra32(rd, rt, shift.value);
    else
      as_dsra(rd, rt, shift.value);
}

void
MacroAssemblerPPC64LE::ma_dror(Register rd, Register rt, Imm32 shift)
{
    if (31 < shift.value)
      as_drotr32(rd, rt, shift.value);
    else
      as_drotr(rd, rt, shift.value);
}

void
MacroAssemblerPPC64LE::ma_drol(Register rd, Register rt, Imm32 shift)
{
    uint32_t s =  64 - shift.value;

    if (31 < s)
      as_drotr32(rd, rt, s);
    else
      as_drotr(rd, rt, s);
}

void
MacroAssemblerPPC64LE::ma_dsll(Register rd, Register rt, Register shift)
{
    as_dsllv(rd, rt, shift);
}

void
MacroAssemblerPPC64LE::ma_dsrl(Register rd, Register rt, Register shift)
{
    as_dsrlv(rd, rt, shift);
}

void
MacroAssemblerPPC64LE::ma_dsra(Register rd, Register rt, Register shift)
{
    as_dsrav(rd, rt, shift);
}

void
MacroAssemblerPPC64LE::ma_dror(Register rd, Register rt, Register shift)
{
    as_drotrv(rd, rt, shift);
}

void
MacroAssemblerPPC64LE::ma_drol(Register rd, Register rt, Register shift)
{
    as_dsubu(ScratchRegister, zero, shift);
    as_drotrv(rd, rt, ScratchRegister);
}

void
MacroAssemblerPPC64LE::ma_dins(Register rt, Register rs, Imm32 pos, Imm32 size)
{
    if (pos.value >= 0 && pos.value < 32) {
        if (pos.value + size.value > 32)
          as_dinsm(rt, rs, pos.value, size.value);
        else
          as_dins(rt, rs, pos.value, size.value);
    } else {
        as_dinsu(rt, rs, pos.value, size.value);
    }
}

void
MacroAssemblerPPC64LE::ma_dext(Register rt, Register rs, Imm32 pos, Imm32 size)
{
    if (pos.value >= 0 && pos.value < 32) {
        if (size.value > 32)
          as_dextm(rt, rs, pos.value, size.value);
        else
          as_dext(rt, rs, pos.value, size.value);
    } else {
        as_dextu(rt, rs, pos.value, size.value);
    }
}

void
MacroAssemblerPPC64LE::ma_dctz(Register rd, Register rs)
{
    ma_dnegu(ScratchRegister, rs);
    as_and(rd, ScratchRegister, rs);
    as_dclz(rd, rd);
    ma_dnegu(SecondScratchReg, rd);
    ma_daddu(SecondScratchReg, Imm32(0x3f));
    as_movn(rd, SecondScratchReg, ScratchRegister);
}

// Arithmetic-based ops.

// Add.
void
MacroAssemblerPPC64LE::ma_daddu(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInSignedRange(imm.value)) {
        as_daddiu(rd, rs, imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_daddu(rd, rs, ScratchRegister);
    }
}

void
MacroAssemblerPPC64LE::ma_daddu(Register rd, Register rs)
{
    as_daddu(rd, rd, rs);
}

void
MacroAssemblerPPC64LE::ma_daddu(Register rd, Imm32 imm)
{
    ma_daddu(rd, rd, imm);
}

void
MacroAssemblerPPC64LE::ma_addTestOverflow(Register rd, Register rs, Register rt, Label* overflow)
{
    as_daddu(SecondScratchReg, rs, rt);
    as_addu(rd, rs, rt);
    ma_b(rd, SecondScratchReg, overflow, Assembler::NotEqual);
}

void
MacroAssemblerPPC64LE::ma_addTestOverflow(Register rd, Register rs, Imm32 imm, Label* overflow)
{
    // Check for signed range because of as_daddiu
    if (Imm16::IsInSignedRange(imm.value)) {
        as_daddiu(SecondScratchReg, rs, imm.value);
        as_addiu(rd, rs, imm.value);
        ma_b(rd, SecondScratchReg, overflow, Assembler::NotEqual);
    } else {
        ma_li(ScratchRegister, imm);
        ma_addTestOverflow(rd, rs, ScratchRegister, overflow);
    }
}

// Subtract.
void
MacroAssemblerPPC64LE::ma_dsubu(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInSignedRange(-imm.value)) {
        as_daddiu(rd, rs, -imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_dsubu(rd, rs, ScratchRegister);
    }
}

void
MacroAssemblerPPC64LE::ma_dsubu(Register rd, Register rs)
{
    as_dsubu(rd, rd, rs);
}

void
MacroAssemblerPPC64LE::ma_dsubu(Register rd, Imm32 imm)
{
    ma_dsubu(rd, rd, imm);
}

void
MacroAssemblerPPC64LE::ma_subTestOverflow(Register rd, Register rs, Register rt, Label* overflow)
{
    as_dsubu(SecondScratchReg, rs, rt);
    as_subu(rd, rs, rt);
    ma_b(rd, SecondScratchReg, overflow, Assembler::NotEqual);
}

void
MacroAssemblerPPC64LE::ma_dmult(Register rs, Imm32 imm)
{
    ma_li(ScratchRegister, imm);
    as_dmult(rs, ScratchRegister);
}

// Memory.

void
MacroAssemblerPPC64LE::ma_load(Register dest, Address address,
                              LoadStoreSize size, LoadStoreExtension extension)
{
    int16_t encodedOffset;
    Register base;

    if (isLoongson() && ZeroExtend != extension &&
        !Imm16::IsInSignedRange(address.offset))
    {
        ma_li(ScratchRegister, Imm32(address.offset));
        base = address.base;

        switch (size) {
          case SizeByte:
            as_gslbx(dest, base, ScratchRegister, 0);
            break;
          case SizeHalfWord:
            as_gslhx(dest, base, ScratchRegister, 0);
            break;
          case SizeWord:
            as_gslwx(dest, base, ScratchRegister, 0);
            break;
          case SizeDouble:
            as_gsldx(dest, base, ScratchRegister, 0);
            break;
          default:
            MOZ_CRASH("Invalid argument for ma_load");
        }
        return;
    }

    if (!Imm16::IsInSignedRange(address.offset)) {
        ma_li(ScratchRegister, Imm32(address.offset));
        as_daddu(ScratchRegister, address.base, ScratchRegister);
        base = ScratchRegister;
        encodedOffset = Imm16(0).encode();
    } else {
        encodedOffset = Imm16(address.offset).encode();
        base = address.base;
    }

    switch (size) {
      case SizeByte:
        if (ZeroExtend == extension)
            as_lbu(dest, base, encodedOffset);
        else
            as_lb(dest, base, encodedOffset);
        break;
      case SizeHalfWord:
        if (ZeroExtend == extension)
            as_lhu(dest, base, encodedOffset);
        else
            as_lh(dest, base, encodedOffset);
        break;
      case SizeWord:
        if (ZeroExtend == extension)
            as_lwu(dest, base, encodedOffset);
        else
            as_lw(dest, base, encodedOffset);
        break;
      case SizeDouble:
        as_ld(dest, base, encodedOffset);
        break;
      default:
        MOZ_CRASH("Invalid argument for ma_load");
    }
}

void
MacroAssemblerPPC64LE::ma_store(Register data, Address address, LoadStoreSize size,
                               LoadStoreExtension extension)
{
    int16_t encodedOffset;
    Register base;

    if (isLoongson() && !Imm16::IsInSignedRange(address.offset)) {
        ma_li(ScratchRegister, Imm32(address.offset));
        base = address.base;

        switch (size) {
          case SizeByte:
            as_gssbx(data, base, ScratchRegister, 0);
            break;
          case SizeHalfWord:
            as_gsshx(data, base, ScratchRegister, 0);
            break;
          case SizeWord:
            as_gsswx(data, base, ScratchRegister, 0);
            break;
          case SizeDouble:
            as_gssdx(data, base, ScratchRegister, 0);
            break;
          default:
            MOZ_CRASH("Invalid argument for ma_store");
        }
        return;
    }

    if (!Imm16::IsInSignedRange(address.offset)) {
        ma_li(ScratchRegister, Imm32(address.offset));
        as_daddu(ScratchRegister, address.base, ScratchRegister);
        base = ScratchRegister;
        encodedOffset = Imm16(0).encode();
    } else {
        encodedOffset = Imm16(address.offset).encode();
        base = address.base;
    }

    switch (size) {
      case SizeByte:
        as_sb(data, base, encodedOffset);
        break;
      case SizeHalfWord:
        as_sh(data, base, encodedOffset);
        break;
      case SizeWord:
        as_sw(data, base, encodedOffset);
        break;
      case SizeDouble:
        as_sd(data, base, encodedOffset);
        break;
      default:
        MOZ_CRASH("Invalid argument for ma_store");
    }
}

void
MacroAssemblerPPC64LECompat::computeScaledAddress(const BaseIndex& address, Register dest)
{
    int32_t shift = Imm32::ShiftOf(address.scale).value;
    if (shift) {
        ma_dsll(ScratchRegister, address.index, Imm32(shift));
        as_daddu(dest, address.base, ScratchRegister);
    } else {
        as_daddu(dest, address.base, address.index);
    }
}

// Shortcut for when we know we're transferring 32 bits of data.
void
MacroAssemblerPPC64LE::ma_pop(Register r)
{
    as_ld(r, StackPointer, 0);
    as_daddiu(StackPointer, StackPointer, sizeof(intptr_t));
}

void
MacroAssemblerPPC64LE::ma_push(Register r)
{
    if (r == sp) {
        // Pushing sp requires one more instruction.
        ma_move(ScratchRegister, sp);
        r = ScratchRegister;
    }

    as_daddiu(StackPointer, StackPointer, (int32_t)-sizeof(intptr_t));
    as_sd(r, StackPointer, 0);
}

// Branches when done from within mips-specific code.
void
MacroAssemblerPPC64LE::ma_b(Register lhs, ImmWord imm, Label* label, Condition c, JumpKind jumpKind)
{
    if (imm.value <= INT32_MAX) {
        ma_b(lhs, Imm32(uint32_t(imm.value)), label, c, jumpKind);
    } else {
        MOZ_ASSERT(lhs != ScratchRegister);
        ma_li(ScratchRegister, imm);
        ma_b(lhs, ScratchRegister, label, c, jumpKind);
    }
}

void
MacroAssemblerPPC64LE::ma_b(Register lhs, Address addr, Label* label, Condition c, JumpKind jumpKind)
{
    MOZ_ASSERT(lhs != ScratchRegister);
    ma_load(ScratchRegister, addr, SizeDouble);
    ma_b(lhs, ScratchRegister, label, c, jumpKind);
}

void
MacroAssemblerPPC64LE::ma_b(Address addr, Imm32 imm, Label* label, Condition c, JumpKind jumpKind)
{
    ma_load(SecondScratchReg, addr, SizeDouble);
    ma_b(SecondScratchReg, imm, label, c, jumpKind);
}

void
MacroAssemblerPPC64LE::ma_b(Address addr, ImmGCPtr imm, Label* label, Condition c, JumpKind jumpKind)
{
    ma_load(SecondScratchReg, addr, SizeDouble);
    ma_b(SecondScratchReg, imm, label, c, jumpKind);
}

void
MacroAssemblerPPC64LE::ma_bal(Label* label, DelaySlotFill delaySlotFill)
{
    spew("branch .Llabel %p\n", label);
    if (label->bound()) {
        // Generate the long jump for calls because return address has to be
        // the address after the reserved block.
        addLongJump(nextOffset(), BufferOffset(label->offset()));
        ma_liPatchable(ScratchRegister, ImmWord(LabelBase::INVALID_OFFSET));
        as_jalr(ScratchRegister);
        if (delaySlotFill == FillDelaySlot)
            as_nop();
        return;
    }

    // Second word holds a pointer to the next branch in label's chain.
    uint32_t nextInChain = label->used() ? label->offset() : LabelBase::INVALID_OFFSET;

    // Make the whole branch continous in the buffer. The '6'
    // instructions are writing at below (contain delay slot).
    m_buffer.ensureSpace(6 * sizeof(uint32_t));

    spew("bal .Llabel %p\n", label);
    BufferOffset bo = writeInst(getBranchCode(BranchIsCall).encode());
    writeInst(nextInChain);
    if (!oom())
        label->use(bo.getOffset());
    // Leave space for long jump.
    as_nop();
    as_nop();
    as_nop();
    if (delaySlotFill == FillDelaySlot)
        as_nop();
}

void
MacroAssemblerPPC64LE::branchWithCode(InstImm code, Label* label, JumpKind jumpKind)
{
    // simply output the pointer of one label as its id,
    // notice that after one label destructor, the pointer will be reused.
    spew("branch .Llabel %p", label);
    MOZ_ASSERT(code.encode() != InstImm(op_regimm, zero, rt_bgezal, BOffImm16(0)).encode());
    InstImm inst_beq = InstImm(op_beq, zero, zero, BOffImm16(0));

    if (label->bound()) {
        int32_t offset = label->offset() - m_buffer.nextOffset().getOffset();

        if (BOffImm16::IsInRange(offset))
            jumpKind = ShortJump;

        if (jumpKind == ShortJump) {
            MOZ_ASSERT(BOffImm16::IsInRange(offset));
            code.setBOffImm16(BOffImm16(offset));
#ifdef JS_JITSPEW
            decodeBranchInstAndSpew(code);
#endif
            writeInst(code.encode());
            as_nop();
            return;
        }

        if (code.encode() == inst_beq.encode()) {
            // Handle long jump
            addLongJump(nextOffset(), BufferOffset(label->offset()));
            ma_liPatchable(ScratchRegister, ImmWord(LabelBase::INVALID_OFFSET));
            as_jr(ScratchRegister);
            as_nop();
            return;
        }

        // Handle long conditional branch, the target offset is based on self,
        // point to next instruction of nop at below.
        spew("invert branch .Llabel %p", label);
        InstImm code_r = invertBranch(code, BOffImm16(7 * sizeof(uint32_t)));
#ifdef JS_JITSPEW
        decodeBranchInstAndSpew(code_r);
#endif
        writeInst(code_r.encode());
        // No need for a "nop" here because we can clobber scratch.
        addLongJump(nextOffset(), BufferOffset(label->offset()));
        ma_liPatchable(ScratchRegister, ImmWord(LabelBase::INVALID_OFFSET));
        as_jr(ScratchRegister);
        as_nop();
        return;
    }

    // Generate open jump and link it to a label.

    // Second word holds a pointer to the next branch in label's chain.
    uint32_t nextInChain = label->used() ? label->offset() : LabelBase::INVALID_OFFSET;

    if (jumpKind == ShortJump) {
        // Make the whole branch continous in the buffer.
        m_buffer.ensureSpace(2 * sizeof(uint32_t));

        // Indicate that this is short jump with offset 4.
        code.setBOffImm16(BOffImm16(4));
#ifdef JS_JITSPEW
        decodeBranchInstAndSpew(code);
#endif
        BufferOffset bo = writeInst(code.encode());
        writeInst(nextInChain);
        if (!oom())
            label->use(bo.getOffset());
        return;
    }

    bool conditional = code.encode() != inst_beq.encode();

    // Make the whole branch continous in the buffer. The '7'
    // instructions are writing at below (contain conditional nop).
    m_buffer.ensureSpace(7 * sizeof(uint32_t));

#ifdef JS_JITSPEW
    decodeBranchInstAndSpew(code);
#endif
    BufferOffset bo = writeInst(code.encode());
    writeInst(nextInChain);
    if (!oom())
        label->use(bo.getOffset());
    // Leave space for potential long jump.
    as_nop();
    as_nop();
    as_nop();
    as_nop();
    if (conditional)
        as_nop();
}

void
MacroAssemblerPPC64LE::ma_cmp_set(Register rd, Register rs, ImmWord imm, Condition c)
{
    if (imm.value <= INT32_MAX) {
        ma_cmp_set(rd, rs, Imm32(uint32_t(imm.value)), c);
    } else {
        ma_li(ScratchRegister, imm);
        ma_cmp_set(rd, rs, ScratchRegister, c);
    }
}

void
MacroAssemblerPPC64LE::ma_cmp_set(Register rd, Register rs, ImmPtr imm, Condition c)
{
    ma_cmp_set(rd, rs, ImmWord(uintptr_t(imm.value)), c);
}

// fp instructions
void
MacroAssemblerPPC64LE::ma_lid(FloatRegister dest, double value)
{
    ImmWord imm(mozilla::BitwiseCast<uint64_t>(value));

    if(imm.value != 0){
        ma_li(ScratchRegister, imm);
        moveToDouble(ScratchRegister, dest);
    } else {
        moveToDouble(zero, dest);
    }

}

void
MacroAssemblerPPC64LE::ma_mv(FloatRegister src, ValueOperand dest)
{
    as_dmfc1(dest.valueReg(), src);
}

void
MacroAssemblerPPC64LE::ma_mv(ValueOperand src, FloatRegister dest)
{
    as_dmtc1(src.valueReg(), dest);
}

void
MacroAssemblerPPC64LE::ma_ls(FloatRegister ft, Address address)
{
    if (Imm16::IsInSignedRange(address.offset)) {
        as_lwc1(ft, address.base, address.offset);
    } else {
        MOZ_ASSERT(address.base != ScratchRegister);
        ma_li(ScratchRegister, Imm32(address.offset));
        if (isLoongson()) {
            as_gslsx(ft, address.base, ScratchRegister, 0);
        } else {
            as_daddu(ScratchRegister, address.base, ScratchRegister);
            as_lwc1(ft, ScratchRegister, 0);
        }
    }
}

void
MacroAssemblerPPC64LE::ma_ld(FloatRegister ft, Address address)
{
    if (Imm16::IsInSignedRange(address.offset)) {
        as_ldc1(ft, address.base, address.offset);
    } else {
        MOZ_ASSERT(address.base != ScratchRegister);
        ma_li(ScratchRegister, Imm32(address.offset));
        if (isLoongson()) {
            as_gsldx(ft, address.base, ScratchRegister, 0);
        } else {
            as_daddu(ScratchRegister, address.base, ScratchRegister);
            as_ldc1(ft, ScratchRegister, 0);
        }
    }
}

void
MacroAssemblerPPC64LE::ma_sd(FloatRegister ft, Address address)
{
    if (Imm16::IsInSignedRange(address.offset)) {
        as_sdc1(ft, address.base, address.offset);
    } else {
        MOZ_ASSERT(address.base != ScratchRegister);
        ma_li(ScratchRegister, Imm32(address.offset));
        if (isLoongson()) {
            as_gssdx(ft, address.base, ScratchRegister, 0);
        } else {
            as_daddu(ScratchRegister, address.base, ScratchRegister);
            as_sdc1(ft, ScratchRegister, 0);
        }
    }
}

void
MacroAssemblerPPC64LE::ma_ss(FloatRegister ft, Address address)
{
    if (Imm16::IsInSignedRange(address.offset)) {
        as_swc1(ft, address.base, address.offset);
    } else {
        MOZ_ASSERT(address.base != ScratchRegister);
        ma_li(ScratchRegister, Imm32(address.offset));
        if (isLoongson()) {
            as_gsssx(ft, address.base, ScratchRegister, 0);
        } else {
            as_daddu(ScratchRegister, address.base, ScratchRegister);
            as_swc1(ft, ScratchRegister, 0);
        }
    }
}

void
MacroAssemblerPPC64LE::ma_pop(FloatRegister f)
{
    as_ldc1(f, StackPointer, 0);
    as_daddiu(StackPointer, StackPointer, sizeof(double));
}

void
MacroAssemblerPPC64LE::ma_push(FloatRegister f)
{
    as_daddiu(StackPointer, StackPointer, (int32_t)-sizeof(double));
    as_sdc1(f, StackPointer, 0);
}

bool
MacroAssemblerPPC64LECompat::buildOOLFakeExitFrame(void* fakeReturnAddr)
{
    uint32_t descriptor = MakeFrameDescriptor(asMasm().framePushed(), JitFrame_IonJS,
                                              ExitFrameLayout::Size());

    asMasm().Push(Imm32(descriptor)); // descriptor_
    asMasm().Push(ImmPtr(fakeReturnAddr));

    return true;
}

void
MacroAssemblerPPC64LECompat::move32(Imm32 imm, Register dest)
{
    ma_li(dest, imm);
}

void
MacroAssemblerPPC64LECompat::move32(Register src, Register dest)
{
    ma_move(dest, src);
}

void
MacroAssemblerPPC64LECompat::movePtr(Register src, Register dest)
{
    ma_move(dest, src);
}
void
MacroAssemblerPPC64LECompat::movePtr(ImmWord imm, Register dest)
{
    ma_li(dest, imm);
}

void
MacroAssemblerPPC64LECompat::movePtr(ImmGCPtr imm, Register dest)
{
    ma_li(dest, imm);
}

void
MacroAssemblerPPC64LECompat::movePtr(ImmPtr imm, Register dest)
{
    movePtr(ImmWord(uintptr_t(imm.value)), dest);
}
void
MacroAssemblerPPC64LECompat::movePtr(wasm::SymbolicAddress imm, Register dest)
{
    append(wasm::SymbolicAccess(CodeOffset(nextOffset().getOffset()), imm));
    ma_liPatchable(dest, ImmWord(-1));
}

void
MacroAssemblerPPC64LECompat::load8ZeroExtend(const Address& address, Register dest)
{
    ma_load(dest, address, SizeByte, ZeroExtend);
}

void
MacroAssemblerPPC64LECompat::load8ZeroExtend(const BaseIndex& src, Register dest)
{
    ma_load(dest, src, SizeByte, ZeroExtend);
}

void
MacroAssemblerPPC64LECompat::load8SignExtend(const Address& address, Register dest)
{
    ma_load(dest, address, SizeByte, SignExtend);
}

void
MacroAssemblerPPC64LECompat::load8SignExtend(const BaseIndex& src, Register dest)
{
    ma_load(dest, src, SizeByte, SignExtend);
}

void
MacroAssemblerPPC64LECompat::load16ZeroExtend(const Address& address, Register dest)
{
    ma_load(dest, address, SizeHalfWord, ZeroExtend);
}

void
MacroAssemblerPPC64LECompat::load16ZeroExtend(const BaseIndex& src, Register dest)
{
    ma_load(dest, src, SizeHalfWord, ZeroExtend);
}

void
MacroAssemblerPPC64LECompat::load16SignExtend(const Address& address, Register dest)
{
    ma_load(dest, address, SizeHalfWord, SignExtend);
}

void
MacroAssemblerPPC64LECompat::load16SignExtend(const BaseIndex& src, Register dest)
{
    ma_load(dest, src, SizeHalfWord, SignExtend);
}

void
MacroAssemblerPPC64LECompat::load32(const Address& address, Register dest)
{
    ma_load(dest, address, SizeWord);
}

void
MacroAssemblerPPC64LECompat::load32(const BaseIndex& address, Register dest)
{
    ma_load(dest, address, SizeWord);
}

void
MacroAssemblerPPC64LECompat::load32(AbsoluteAddress address, Register dest)
{
    movePtr(ImmPtr(address.addr), ScratchRegister);
    load32(Address(ScratchRegister, 0), dest);
}

void
MacroAssemblerPPC64LECompat::load32(wasm::SymbolicAddress address, Register dest)
{
    movePtr(address, ScratchRegister);
    load32(Address(ScratchRegister, 0), dest);
}

void
MacroAssemblerPPC64LECompat::loadPtr(const Address& address, Register dest)
{
    ma_load(dest, address, SizeDouble);
}

void
MacroAssemblerPPC64LECompat::loadPtr(const BaseIndex& src, Register dest)
{
    ma_load(dest, src, SizeDouble);
}

void
MacroAssemblerPPC64LECompat::loadPtr(AbsoluteAddress address, Register dest)
{
    movePtr(ImmPtr(address.addr), ScratchRegister);
    loadPtr(Address(ScratchRegister, 0), dest);
}

void
MacroAssemblerPPC64LECompat::loadPtr(wasm::SymbolicAddress address, Register dest)
{
    movePtr(address, ScratchRegister);
    loadPtr(Address(ScratchRegister, 0), dest);
}

void
MacroAssemblerPPC64LECompat::loadPrivate(const Address& address, Register dest)
{
    loadPtr(address, dest);
    ma_dsll(dest, dest, Imm32(1));
}

void
MacroAssemblerPPC64LECompat::loadUnalignedDouble(const wasm::MemoryAccessDesc& access,
                                                const BaseIndex& src, Register temp, FloatRegister dest)
{
    computeScaledAddress(src, SecondScratchReg);
    BufferOffset load;
    if (Imm16::IsInSignedRange(src.offset) && Imm16::IsInSignedRange(src.offset + 7)) {
        load = as_ldl(temp, SecondScratchReg, src.offset + 7);
        as_ldr(temp, SecondScratchReg, src.offset);
    } else {
        ma_li(ScratchRegister, Imm32(src.offset));
        as_daddu(ScratchRegister, SecondScratchReg, ScratchRegister);
        load = as_ldl(temp, ScratchRegister, 7);
        as_ldr(temp, ScratchRegister, 0);
    }
    append(access, load.getOffset());
    moveToDouble(temp, dest);
}

void
MacroAssemblerPPC64LECompat::loadUnalignedFloat32(const wasm::MemoryAccessDesc& access,
                                                 const BaseIndex& src, Register temp, FloatRegister dest)
{
    computeScaledAddress(src, SecondScratchReg);
    BufferOffset load;
    if (Imm16::IsInSignedRange(src.offset) && Imm16::IsInSignedRange(src.offset + 3)) {
        load = as_lwl(temp, SecondScratchReg, src.offset + 3);
        as_lwr(temp, SecondScratchReg, src.offset);
    } else {
        ma_li(ScratchRegister, Imm32(src.offset));
        as_daddu(ScratchRegister, SecondScratchReg, ScratchRegister);
        load = as_lwl(temp, ScratchRegister, 3);
        as_lwr(temp, ScratchRegister, 0);
    }
    append(access, load.getOffset());
    moveToFloat32(temp, dest);
}

void
MacroAssemblerPPC64LECompat::store8(Imm32 imm, const Address& address)
{
    ma_li(SecondScratchReg, imm);
    ma_store(SecondScratchReg, address, SizeByte);
}

void
MacroAssemblerPPC64LECompat::store8(Register src, const Address& address)
{
    ma_store(src, address, SizeByte);
}

void
MacroAssemblerPPC64LECompat::store8(Imm32 imm, const BaseIndex& dest)
{
    ma_store(imm, dest, SizeByte);
}

void
MacroAssemblerPPC64LECompat::store8(Register src, const BaseIndex& dest)
{
    ma_store(src, dest, SizeByte);
}

void
MacroAssemblerPPC64LECompat::store16(Imm32 imm, const Address& address)
{
    ma_li(SecondScratchReg, imm);
    ma_store(SecondScratchReg, address, SizeHalfWord);
}

void
MacroAssemblerPPC64LECompat::store16(Register src, const Address& address)
{
    ma_store(src, address, SizeHalfWord);
}

void
MacroAssemblerPPC64LECompat::store16(Imm32 imm, const BaseIndex& dest)
{
    ma_store(imm, dest, SizeHalfWord);
}

void
MacroAssemblerPPC64LECompat::store16(Register src, const BaseIndex& address)
{
    ma_store(src, address, SizeHalfWord);
}

void
MacroAssemblerPPC64LECompat::store32(Register src, AbsoluteAddress address)
{
    movePtr(ImmPtr(address.addr), ScratchRegister);
    store32(src, Address(ScratchRegister, 0));
}

void
MacroAssemblerPPC64LECompat::store32(Register src, const Address& address)
{
    ma_store(src, address, SizeWord);
}

void
MacroAssemblerPPC64LECompat::store32(Imm32 src, const Address& address)
{
    move32(src, SecondScratchReg);
    ma_store(SecondScratchReg, address, SizeWord);
}

void
MacroAssemblerPPC64LECompat::store32(Imm32 imm, const BaseIndex& dest)
{
    ma_store(imm, dest, SizeWord);
}

void
MacroAssemblerPPC64LECompat::store32(Register src, const BaseIndex& dest)
{
    ma_store(src, dest, SizeWord);
}

template <typename T>
void
MacroAssemblerPPC64LECompat::storePtr(ImmWord imm, T address)
{
    ma_li(SecondScratchReg, imm);
    ma_store(SecondScratchReg, address, SizeDouble);
}

template void MacroAssemblerPPC64LECompat::storePtr<Address>(ImmWord imm, Address address);
template void MacroAssemblerPPC64LECompat::storePtr<BaseIndex>(ImmWord imm, BaseIndex address);

template <typename T>
void
MacroAssemblerPPC64LECompat::storePtr(ImmPtr imm, T address)
{
    storePtr(ImmWord(uintptr_t(imm.value)), address);
}

template void MacroAssemblerPPC64LECompat::storePtr<Address>(ImmPtr imm, Address address);
template void MacroAssemblerPPC64LECompat::storePtr<BaseIndex>(ImmPtr imm, BaseIndex address);

template <typename T>
void
MacroAssemblerPPC64LECompat::storePtr(ImmGCPtr imm, T address)
{
    movePtr(imm, SecondScratchReg);
    storePtr(SecondScratchReg, address);
}

template void MacroAssemblerPPC64LECompat::storePtr<Address>(ImmGCPtr imm, Address address);
template void MacroAssemblerPPC64LECompat::storePtr<BaseIndex>(ImmGCPtr imm, BaseIndex address);

void
MacroAssemblerPPC64LECompat::storePtr(Register src, const Address& address)
{
    ma_store(src, address, SizeDouble);
}

void
MacroAssemblerPPC64LECompat::storePtr(Register src, const BaseIndex& address)
{
    ma_store(src, address, SizeDouble);
}

void
MacroAssemblerPPC64LECompat::storePtr(Register src, AbsoluteAddress dest)
{
    movePtr(ImmPtr(dest.addr), ScratchRegister);
    storePtr(src, Address(ScratchRegister, 0));
}

void
MacroAssemblerPPC64LECompat::storeUnalignedFloat32(const wasm::MemoryAccessDesc& access,
                                                  FloatRegister src, Register temp, const BaseIndex& dest)
{
    computeScaledAddress(dest, SecondScratchReg);
    moveFromFloat32(src, temp);
    BufferOffset store;
    if (Imm16::IsInSignedRange(dest.offset) && Imm16::IsInSignedRange(dest.offset + 3)) {
        store = as_swl(temp, SecondScratchReg, dest.offset + 3);
        as_swr(temp, SecondScratchReg, dest.offset);
    } else {
        ma_li(ScratchRegister, Imm32(dest.offset));
        as_daddu(ScratchRegister, SecondScratchReg, ScratchRegister);
        store = as_swl(temp, ScratchRegister, 3);
        as_swr(temp, ScratchRegister, 0);
    }
    append(access, store.getOffset());
}

void
MacroAssemblerPPC64LECompat::storeUnalignedDouble(const wasm::MemoryAccessDesc& access,
                                                 FloatRegister src, Register temp, const BaseIndex& dest)
{
    computeScaledAddress(dest, SecondScratchReg);
    moveFromDouble(src, temp);

    BufferOffset store;
    if (Imm16::IsInSignedRange(dest.offset) && Imm16::IsInSignedRange(dest.offset + 7)) {
        store = as_sdl(temp, SecondScratchReg, dest.offset + 7);
        as_sdr(temp, SecondScratchReg, dest.offset);
    } else {
        ma_li(ScratchRegister, Imm32(dest.offset));
        as_daddu(ScratchRegister, SecondScratchReg, ScratchRegister);
        store = as_sdl(temp, ScratchRegister, 7);
        as_sdr(temp, ScratchRegister, 0);
    }
    append(access, store.getOffset());
}

void
MacroAssembler::clampDoubleToUint8(FloatRegister input, Register output)
{
     as_roundwd(ScratchDoubleReg, input);
     ma_li(ScratchRegister, Imm32(255));
     as_mfc1(output, ScratchDoubleReg);
     zeroDouble(ScratchDoubleReg);
     as_sltiu(SecondScratchReg, output, 255);
     as_colt(DoubleFloat, ScratchDoubleReg, input);
     // if res > 255; res = 255;
     as_movz(output, ScratchRegister, SecondScratchReg);
     // if !(input > 0); res = 0;
     as_movf(output, zero);
}

void
MacroAssemblerPPC64LECompat::testNullSet(Condition cond, const ValueOperand& value, Register dest)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    splitTag(value, SecondScratchReg);
    ma_cmp_set(dest, SecondScratchReg, ImmTag(JSVAL_TAG_NULL), cond);
}

void
MacroAssemblerPPC64LECompat::testObjectSet(Condition cond, const ValueOperand& value, Register dest)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    splitTag(value, SecondScratchReg);
    ma_cmp_set(dest, SecondScratchReg, ImmTag(JSVAL_TAG_OBJECT), cond);
}

void
MacroAssemblerPPC64LECompat::testUndefinedSet(Condition cond, const ValueOperand& value, Register dest)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    splitTag(value, SecondScratchReg);
    ma_cmp_set(dest, SecondScratchReg, ImmTag(JSVAL_TAG_UNDEFINED), cond);
}

void
MacroAssemblerPPC64LECompat::unboxInt32(const ValueOperand& operand, Register dest)
{
    ma_sll(dest, operand.valueReg(), Imm32(0));
}

void
MacroAssemblerPPC64LECompat::unboxInt32(Register src, Register dest)
{
    ma_sll(dest, src, Imm32(0));
}

void
MacroAssemblerPPC64LECompat::unboxInt32(const Address& src, Register dest)
{
    load32(Address(src.base, src.offset), dest);
}

void
MacroAssemblerPPC64LECompat::unboxInt32(const BaseIndex& src, Register dest)
{
    computeScaledAddress(src, SecondScratchReg);
    load32(Address(SecondScratchReg, src.offset), dest);
}

void
MacroAssemblerPPC64LECompat::unboxBoolean(const ValueOperand& operand, Register dest)
{
    ma_dext(dest, operand.valueReg(), Imm32(0), Imm32(32));
}

void
MacroAssemblerPPC64LECompat::unboxBoolean(Register src, Register dest)
{
    ma_dext(dest, src, Imm32(0), Imm32(32));
}

void
MacroAssemblerPPC64LECompat::unboxBoolean(const Address& src, Register dest)
{
    ma_load(dest, Address(src.base, src.offset), SizeWord, ZeroExtend);
}

void
MacroAssemblerPPC64LECompat::unboxBoolean(const BaseIndex& src, Register dest)
{
    computeScaledAddress(src, SecondScratchReg);
    ma_load(dest, Address(SecondScratchReg, src.offset), SizeWord, ZeroExtend);
}

void
MacroAssemblerPPC64LECompat::unboxDouble(const ValueOperand& operand, FloatRegister dest)
{
    as_dmtc1(operand.valueReg(), dest);
}

void
MacroAssemblerPPC64LECompat::unboxDouble(const Address& src, FloatRegister dest)
{
    ma_ld(dest, Address(src.base, src.offset));
}

void
MacroAssemblerPPC64LECompat::unboxString(const ValueOperand& operand, Register dest)
{
    unboxNonDouble(operand, dest, JSVAL_TYPE_STRING);
}

void
MacroAssemblerPPC64LECompat::unboxString(Register src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_STRING);
}

void
MacroAssemblerPPC64LECompat::unboxString(const Address& src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_STRING);
}

void
MacroAssemblerPPC64LECompat::unboxSymbol(const ValueOperand& operand, Register dest)
{
    unboxNonDouble(operand, dest, JSVAL_TYPE_SYMBOL);
}

void
MacroAssemblerPPC64LECompat::unboxSymbol(Register src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_SYMBOL);
}

void
MacroAssemblerPPC64LECompat::unboxSymbol(const Address& src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_SYMBOL);
}

void
MacroAssemblerPPC64LECompat::unboxObject(const ValueOperand& src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_OBJECT);
}

void
MacroAssemblerPPC64LECompat::unboxObject(Register src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_OBJECT);
}

void
MacroAssemblerPPC64LECompat::unboxObject(const Address& src, Register dest)
{
    unboxNonDouble(src, dest, JSVAL_TYPE_OBJECT);
}

void
MacroAssemblerPPC64LECompat::unboxValue(const ValueOperand& src, AnyRegister dest, JSValueType type)
{
    if (dest.isFloat()) {
        Label notInt32, end;
        asMasm().branchTestInt32(Assembler::NotEqual, src, &notInt32);
        convertInt32ToDouble(src.valueReg(), dest.fpu());
        ma_b(&end, ShortJump);
        bind(&notInt32);
        unboxDouble(src, dest.fpu());
        bind(&end);
    } else {
        unboxNonDouble(src, dest.gpr(), type);
    }
}

void
MacroAssemblerPPC64LECompat::unboxPrivate(const ValueOperand& src, Register dest)
{
    ma_dsll(dest, src.valueReg(), Imm32(1));
}

void
MacroAssemblerPPC64LECompat::boxDouble(FloatRegister src, const ValueOperand& dest, FloatRegister)
{
    as_dmfc1(dest.valueReg(), src);
}

void
MacroAssemblerPPC64LECompat::boxNonDouble(JSValueType type, Register src,
                                         const ValueOperand& dest)
{
    MOZ_ASSERT(src != dest.valueReg());
    boxValue(type, src, dest.valueReg());
}

void
MacroAssemblerPPC64LECompat::boolValueToDouble(const ValueOperand& operand, FloatRegister dest)
{
    convertBoolToInt32(operand.valueReg(), ScratchRegister);
    convertInt32ToDouble(ScratchRegister, dest);
}

void
MacroAssemblerPPC64LECompat::int32ValueToDouble(const ValueOperand& operand,
                                               FloatRegister dest)
{
    convertInt32ToDouble(operand.valueReg(), dest);
}

void
MacroAssemblerPPC64LECompat::boolValueToFloat32(const ValueOperand& operand,
                                               FloatRegister dest)
{

    convertBoolToInt32(operand.valueReg(), ScratchRegister);
    convertInt32ToFloat32(ScratchRegister, dest);
}

void
MacroAssemblerPPC64LECompat::int32ValueToFloat32(const ValueOperand& operand,
                                                FloatRegister dest)
{
    convertInt32ToFloat32(operand.valueReg(), dest);
}

void
MacroAssemblerPPC64LECompat::loadConstantFloat32(float f, FloatRegister dest)
{
    ma_lis(dest, f);
}

void
MacroAssemblerPPC64LECompat::loadInt32OrDouble(const Address& src, FloatRegister dest)
{
    Label notInt32, end;
    // If it's an int, convert it to double.
    loadPtr(Address(src.base, src.offset), ScratchRegister);
    ma_dsrl(SecondScratchReg, ScratchRegister, Imm32(JSVAL_TAG_SHIFT));
    asMasm().branchTestInt32(Assembler::NotEqual, SecondScratchReg, &notInt32);
    loadPtr(Address(src.base, src.offset), SecondScratchReg);
    convertInt32ToDouble(SecondScratchReg, dest);
    ma_b(&end, ShortJump);

    // Not an int, just load as double.
    bind(&notInt32);
    ma_ld(dest, src);
    bind(&end);
}

void
MacroAssemblerPPC64LECompat::loadInt32OrDouble(const BaseIndex& addr, FloatRegister dest)
{
    Label notInt32, end;

    // If it's an int, convert it to double.
    computeScaledAddress(addr, SecondScratchReg);
    // Since we only have one scratch, we need to stomp over it with the tag.
    loadPtr(Address(SecondScratchReg, 0), ScratchRegister);
    ma_dsrl(SecondScratchReg, ScratchRegister, Imm32(JSVAL_TAG_SHIFT));
    asMasm().branchTestInt32(Assembler::NotEqual, SecondScratchReg, &notInt32);

    computeScaledAddress(addr, SecondScratchReg);
    loadPtr(Address(SecondScratchReg, 0), SecondScratchReg);
    convertInt32ToDouble(SecondScratchReg, dest);
    ma_b(&end, ShortJump);

    // Not an int, just load as double.
    bind(&notInt32);
    // First, recompute the offset that had been stored in the scratch register
    // since the scratch register was overwritten loading in the type.
    computeScaledAddress(addr, SecondScratchReg);
    loadDouble(Address(SecondScratchReg, 0), dest);
    bind(&end);
}

void
MacroAssemblerPPC64LECompat::loadConstantDouble(double dp, FloatRegister dest)
{
    ma_lid(dest, dp);
}

Register
MacroAssemblerPPC64LECompat::extractObject(const Address& address, Register scratch)
{
    loadPtr(Address(address.base, address.offset), scratch);
    ma_dext(scratch, scratch, Imm32(0), Imm32(JSVAL_TAG_SHIFT));
    return scratch;
}

Register
MacroAssemblerPPC64LECompat::extractTag(const Address& address, Register scratch)
{
    loadPtr(Address(address.base, address.offset), scratch);
    ma_dext(scratch, scratch, Imm32(JSVAL_TAG_SHIFT), Imm32(64 - JSVAL_TAG_SHIFT));
    return scratch;
}

Register
MacroAssemblerPPC64LECompat::extractTag(const BaseIndex& address, Register scratch)
{
    computeScaledAddress(address, scratch);
    return extractTag(Address(scratch, address.offset), scratch);
}

CodeOffsetJump
MacroAssemblerPPC64LECompat::jumpWithPatch(RepatchLabel* label)
{
    // Only one branch per label.
    MOZ_ASSERT(!label->used());

    BufferOffset bo = nextOffset();
    label->use(bo.getOffset());
    ma_liPatchable(ScratchRegister, ImmWord(LabelBase::INVALID_OFFSET));
    as_jr(ScratchRegister);
    as_nop();
    return CodeOffsetJump(bo.getOffset());
}

/////////////////////////////////////////////////////////////////
// X86/X64-common/ARM/MIPS interface.
/////////////////////////////////////////////////////////////////
void
MacroAssemblerPPC64LECompat::storeValue(ValueOperand val, Operand dst)
{
    storeValue(val, Address(Register::FromCode(dst.base()), dst.disp()));
}

void
MacroAssemblerPPC64LECompat::storeValue(ValueOperand val, const BaseIndex& dest)
{
    computeScaledAddress(dest, SecondScratchReg);
    storeValue(val, Address(SecondScratchReg, dest.offset));
}

void
MacroAssemblerPPC64LECompat::storeValue(JSValueType type, Register reg, BaseIndex dest)
{
    computeScaledAddress(dest, ScratchRegister);

    int32_t offset = dest.offset;
    if (!Imm16::IsInSignedRange(offset)) {
        ma_li(SecondScratchReg, Imm32(offset));
        as_daddu(ScratchRegister, ScratchRegister, SecondScratchReg);
        offset = 0;
    }

    storeValue(type, reg, Address(ScratchRegister, offset));
}

void
MacroAssemblerPPC64LECompat::storeValue(ValueOperand val, const Address& dest)
{
    storePtr(val.valueReg(), Address(dest.base, dest.offset));
}

void
MacroAssemblerPPC64LECompat::storeValue(JSValueType type, Register reg, Address dest)
{
    MOZ_ASSERT(dest.base != SecondScratchReg);

    if (type == JSVAL_TYPE_INT32 || type == JSVAL_TYPE_BOOLEAN) {
        store32(reg, dest);
        JSValueShiftedTag tag = (JSValueShiftedTag)JSVAL_TYPE_TO_SHIFTED_TAG(type);
        store32(((Imm64(tag)).secondHalf()), Address(dest.base, dest.offset + 4));
    } else {
        ma_li(SecondScratchReg, ImmTag(JSVAL_TYPE_TO_TAG(type)));
        ma_dsll(SecondScratchReg, SecondScratchReg, Imm32(JSVAL_TAG_SHIFT));
        ma_dins(SecondScratchReg, reg, Imm32(0), Imm32(JSVAL_TAG_SHIFT));
        storePtr(SecondScratchReg, Address(dest.base, dest.offset));
    }
}

void
MacroAssemblerPPC64LECompat::storeValue(const Value& val, Address dest)
{
    if (val.isGCThing()) {
        writeDataRelocation(val);
        movWithPatch(ImmWord(val.asRawBits()), SecondScratchReg);
    } else {
        ma_li(SecondScratchReg, ImmWord(val.asRawBits()));
    }
    storePtr(SecondScratchReg, Address(dest.base, dest.offset));
}

void
MacroAssemblerPPC64LECompat::storeValue(const Value& val, BaseIndex dest)
{
    computeScaledAddress(dest, ScratchRegister);

    int32_t offset = dest.offset;
    if (!Imm16::IsInSignedRange(offset)) {
        ma_li(SecondScratchReg, Imm32(offset));
        as_daddu(ScratchRegister, ScratchRegister, SecondScratchReg);
        offset = 0;
    }
    storeValue(val, Address(ScratchRegister, offset));
}

void
MacroAssemblerPPC64LECompat::loadValue(const BaseIndex& addr, ValueOperand val)
{
    computeScaledAddress(addr, SecondScratchReg);
    loadValue(Address(SecondScratchReg, addr.offset), val);
}

void
MacroAssemblerPPC64LECompat::loadValue(Address src, ValueOperand val)
{
    loadPtr(Address(src.base, src.offset), val.valueReg());
}

void
MacroAssemblerPPC64LECompat::tagValue(JSValueType type, Register payload, ValueOperand dest)
{
    MOZ_ASSERT(dest.valueReg() != ScratchRegister);
    if (payload != dest.valueReg())
      ma_move(dest.valueReg(), payload);
    ma_li(ScratchRegister, ImmTag(JSVAL_TYPE_TO_TAG(type)));
    ma_dins(dest.valueReg(), ScratchRegister, Imm32(JSVAL_TAG_SHIFT), Imm32(64 - JSVAL_TAG_SHIFT));
}

void
MacroAssemblerPPC64LECompat::pushValue(ValueOperand val)
{
    // Allocate stack slots for Value. One for each.
    asMasm().subPtr(Imm32(sizeof(Value)), StackPointer);
    // Store Value
    storeValue(val, Address(StackPointer, 0));
}

void
MacroAssemblerPPC64LECompat::pushValue(const Address& addr)
{
    // Load value before allocate stack, addr.base may be is sp.
    loadPtr(Address(addr.base, addr.offset), ScratchRegister);
    ma_dsubu(StackPointer, StackPointer, Imm32(sizeof(Value)));
    storePtr(ScratchRegister, Address(StackPointer, 0));
}

void
MacroAssemblerPPC64LECompat::popValue(ValueOperand val)
{
    as_ld(val.valueReg(), StackPointer, 0);
    as_daddiu(StackPointer, StackPointer, sizeof(Value));
}

void
MacroAssemblerPPC64LECompat::breakpoint()
{
    as_break(0);
}

void
MacroAssemblerPPC64LECompat::ensureDouble(const ValueOperand& source, FloatRegister dest,
                                         Label* failure)
{
    Label isDouble, done;
    {
        ScratchTagScope tag(asMasm(), source);
        splitTagForTest(source, tag);
        asMasm().branchTestDouble(Assembler::Equal, tag, &isDouble);
        asMasm().branchTestInt32(Assembler::NotEqual, tag, failure);
    }

    unboxInt32(source, ScratchRegister);
    convertInt32ToDouble(ScratchRegister, dest);
    jump(&done);

    bind(&isDouble);
    unboxDouble(source, dest);

    bind(&done);
}

void
MacroAssemblerPPC64LECompat::checkStackAlignment()
{
#ifdef DEBUG
    Label aligned;
    as_andi(ScratchRegister, sp, ABIStackAlignment - 1);
    ma_b(ScratchRegister, zero, &aligned, Equal, ShortJump);
    as_break(BREAK_STACK_UNALIGNED);
    bind(&aligned);
#endif
}

void
MacroAssemblerPPC64LECompat::handleFailureWithHandlerTail(void* handler, Label* profilerExitTail)
{
    // Reserve space for exception information.
    int size = (sizeof(ResumeFromException) + ABIStackAlignment) & ~(ABIStackAlignment - 1);
    asMasm().subPtr(Imm32(size), StackPointer);
    ma_move(a0, StackPointer); // Use a0 since it is a first function argument

    // Call the handler.
    asMasm().setupUnalignedABICall(a1);
    asMasm().passABIArg(a0);
    asMasm().callWithABI(handler, MoveOp::GENERAL, CheckUnsafeCallWithABI::DontCheckHasExitFrame);

    Label entryFrame;
    Label catch_;
    Label finally;
    Label return_;
    Label bailout;
    Label wasm;

    // Already clobbered a0, so use it...
    load32(Address(StackPointer, offsetof(ResumeFromException, kind)), a0);
    asMasm().branch32(Assembler::Equal, a0, Imm32(ResumeFromException::RESUME_ENTRY_FRAME),
                      &entryFrame);
    asMasm().branch32(Assembler::Equal, a0, Imm32(ResumeFromException::RESUME_CATCH), &catch_);
    asMasm().branch32(Assembler::Equal, a0, Imm32(ResumeFromException::RESUME_FINALLY), &finally);
    asMasm().branch32(Assembler::Equal, a0, Imm32(ResumeFromException::RESUME_FORCED_RETURN),
                      &return_);
    asMasm().branch32(Assembler::Equal, a0, Imm32(ResumeFromException::RESUME_BAILOUT), &bailout);
    asMasm().branch32(Assembler::Equal, a0, Imm32(ResumeFromException::RESUME_WASM), &wasm);

    breakpoint(); // Invalid kind.

    // No exception handler. Load the error value, load the new stack pointer
    // and return from the entry frame.
    bind(&entryFrame);
    asMasm().moveValue(MagicValue(JS_ION_ERROR), JSReturnOperand);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, stackPointer)), StackPointer);

    // We're going to be returning by the ion calling convention
    ma_pop(ra);
    as_jr(ra);
    as_nop();

    // If we found a catch handler, this must be a baseline frame. Restore
    // state and jump to the catch block.
    bind(&catch_);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, target)), a0);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, framePointer)), BaselineFrameReg);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, stackPointer)), StackPointer);
    jump(a0);

    // If we found a finally block, this must be a baseline frame. Push
    // two values expected by JSOP_RETSUB: BooleanValue(true) and the
    // exception.
    bind(&finally);
    ValueOperand exception = ValueOperand(a1);
    loadValue(Address(sp, offsetof(ResumeFromException, exception)), exception);

    loadPtr(Address(sp, offsetof(ResumeFromException, target)), a0);
    loadPtr(Address(sp, offsetof(ResumeFromException, framePointer)), BaselineFrameReg);
    loadPtr(Address(sp, offsetof(ResumeFromException, stackPointer)), sp);

    pushValue(BooleanValue(true));
    pushValue(exception);
    jump(a0);

    // Only used in debug mode. Return BaselineFrame->returnValue() to the
    // caller.
    bind(&return_);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, framePointer)), BaselineFrameReg);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, stackPointer)), StackPointer);
    loadValue(Address(BaselineFrameReg, BaselineFrame::reverseOffsetOfReturnValue()),
              JSReturnOperand);
    ma_move(StackPointer, BaselineFrameReg);
    pop(BaselineFrameReg);

    // If profiling is enabled, then update the lastProfilingFrame to refer to caller
    // frame before returning.
    {
        Label skipProfilingInstrumentation;
        // Test if profiler enabled.
        AbsoluteAddress addressOfEnabled(GetJitContext()->runtime->geckoProfiler().addressOfEnabled());
        asMasm().branch32(Assembler::Equal, addressOfEnabled, Imm32(0),
                          &skipProfilingInstrumentation);
        jump(profilerExitTail);
        bind(&skipProfilingInstrumentation);
    }

    ret();

    // If we are bailing out to baseline to handle an exception, jump to
    // the bailout tail stub.
    bind(&bailout);
    loadPtr(Address(sp, offsetof(ResumeFromException, bailoutInfo)), a2);
    ma_li(ReturnReg, Imm32(BAILOUT_RETURN_OK));
    loadPtr(Address(sp, offsetof(ResumeFromException, target)), a1);
    jump(a1);

    // If we are throwing and the innermost frame was a wasm frame, reset SP and
    // FP; SP is pointing to the unwound return address to the wasm entry, so
    // we can just ret().
    bind(&wasm);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, framePointer)), FramePointer);
    loadPtr(Address(StackPointer, offsetof(ResumeFromException, stackPointer)), StackPointer);
    ret();
}

CodeOffset
MacroAssemblerPPC64LECompat::toggledJump(Label* label)
{
    CodeOffset ret(nextOffset().getOffset());
    ma_b(label);
    return ret;
}

CodeOffset
MacroAssemblerPPC64LECompat::toggledCall(JitCode* target, bool enabled)
{
    BufferOffset bo = nextOffset();
    CodeOffset offset(bo.getOffset());
    addPendingJump(bo, ImmPtr(target->raw()), Relocation::JITCODE);
    ma_liPatchable(ScratchRegister, ImmPtr(target->raw()));
    if (enabled) {
        as_jalr(ScratchRegister);
        as_nop();
    } else {
        as_nop();
        as_nop();
    }
    MOZ_ASSERT_IF(!oom(), nextOffset().getOffset() - offset.offset() == ToggledCallSize(nullptr));
    return offset;
}

void
MacroAssemblerPPC64LECompat::profilerEnterFrame(Register framePtr, Register scratch)
{
    asMasm().loadJSContext(scratch);
    loadPtr(Address(scratch, offsetof(JSContext, profilingActivation_)), scratch);
    storePtr(framePtr, Address(scratch, JitActivation::offsetOfLastProfilingFrame()));
    storePtr(ImmPtr(nullptr), Address(scratch, JitActivation::offsetOfLastProfilingCallSite()));
}

void
MacroAssemblerPPC64LECompat::profilerExitFrame()
{
    jump(GetJitContext()->runtime->jitRuntime()->getProfilerExitFrameTail());
}

void
MacroAssembler::subFromStackPtr(Imm32 imm32)
{
    if (imm32.value)
        asMasm().subPtr(imm32, StackPointer);
}

//{{{ check_macroassembler_style
// ===============================================================
// Stack manipulation functions.

void
MacroAssembler::PushRegsInMask(LiveRegisterSet set)
{
    int32_t diff = set.gprs().size() * sizeof(intptr_t) +
        set.fpus().getPushSizeInBytes();
    const int32_t reserved = diff;

    reserveStack(reserved);
    for (GeneralRegisterBackwardIterator iter(set.gprs()); iter.more(); ++iter) {
        diff -= sizeof(intptr_t);
        storePtr(*iter, Address(StackPointer, diff));
    }
    for (FloatRegisterBackwardIterator iter(set.fpus().reduceSetForPush()); iter.more(); ++iter) {
        diff -= sizeof(double);
        storeDouble(*iter, Address(StackPointer, diff));
    }
    MOZ_ASSERT(diff == 0);
}

void
MacroAssembler::PopRegsInMaskIgnore(LiveRegisterSet set, LiveRegisterSet ignore)
{
    int32_t diff = set.gprs().size() * sizeof(intptr_t) +
        set.fpus().getPushSizeInBytes();
    const int32_t reserved = diff;

    for (GeneralRegisterBackwardIterator iter(set.gprs()); iter.more(); ++iter) {
        diff -= sizeof(intptr_t);
        if (!ignore.has(*iter))
          loadPtr(Address(StackPointer, diff), *iter);
    }
    for (FloatRegisterBackwardIterator iter(set.fpus().reduceSetForPush()); iter.more(); ++iter) {
        diff -= sizeof(double);
        if (!ignore.has(*iter))
          loadDouble(Address(StackPointer, diff), *iter);
    }
    MOZ_ASSERT(diff == 0);
    freeStack(reserved);
}

void
MacroAssembler::storeRegsInMask(LiveRegisterSet set, Address dest, Register)
{
    FloatRegisterSet fpuSet(set.fpus().reduceSetForPush());
    unsigned numFpu = fpuSet.size();
    int32_t diffF = fpuSet.getPushSizeInBytes();
    int32_t diffG = set.gprs().size() * sizeof(intptr_t);

    MOZ_ASSERT(dest.offset >= diffG + diffF);

    for (GeneralRegisterBackwardIterator iter(set.gprs()); iter.more(); ++iter) {
        diffG -= sizeof(intptr_t);
        dest.offset -= sizeof(intptr_t);
        storePtr(*iter, dest);
    }
    MOZ_ASSERT(diffG == 0);

    for (FloatRegisterBackwardIterator iter(fpuSet); iter.more(); ++iter) {
        FloatRegister reg = *iter;
        diffF -= reg.size();
        numFpu -= 1;
        dest.offset -= reg.size();
        if (reg.isDouble())
            storeDouble(reg, dest);
        else if (reg.isSingle())
            storeFloat32(reg, dest);
        else
            MOZ_CRASH("Unknown register type.");
    }
    MOZ_ASSERT(numFpu == 0);
    diffF -= diffF % sizeof(uintptr_t);
    MOZ_ASSERT(diffF == 0);
}
// ===============================================================
// ABI function calls.

void
MacroAssembler::setupUnalignedABICall(Register scratch)
{
    MOZ_ASSERT(!IsCompilingWasm(), "wasm should only use aligned ABI calls");
    setupABICall();
    dynamicAlignment_ = true;

    ma_move(scratch, StackPointer);

    // Force sp to be aligned
    asMasm().subPtr(Imm32(sizeof(uintptr_t)), StackPointer);
    ma_and(StackPointer, StackPointer, Imm32(~(ABIStackAlignment - 1)));
    storePtr(scratch, Address(StackPointer, 0));
}

void
MacroAssembler::callWithABIPre(uint32_t* stackAdjust, bool callFromWasm)
{
    MOZ_ASSERT(inCall_);
    uint32_t stackForCall = abiArgs_.stackBytesConsumedSoFar();

    // Reserve place for $ra.
    stackForCall += sizeof(intptr_t);

    if (dynamicAlignment_) {
        stackForCall += ComputeByteAlignment(stackForCall, ABIStackAlignment);
    } else {
        uint32_t alignmentAtPrologue = callFromWasm ? sizeof(wasm::Frame) : 0;
        stackForCall += ComputeByteAlignment(stackForCall + framePushed() + alignmentAtPrologue,
                                             ABIStackAlignment);
    }

    *stackAdjust = stackForCall;
    reserveStack(stackForCall);

    // Save $ra because call is going to clobber it. Restore it in
    // callWithABIPost. NOTE: This is needed for calls from SharedIC.
    // Maybe we can do this differently.
    storePtr(ra, Address(StackPointer, stackForCall - sizeof(intptr_t)));

    // Position all arguments.
    {
        enoughMemory_ &= moveResolver_.resolve();
        if (!enoughMemory_)
            return;

        MoveEmitter emitter(*this);
        emitter.emit(moveResolver_);
        emitter.finish();
    }

    assertStackAlignment(ABIStackAlignment);
}

void
MacroAssembler::callWithABIPost(uint32_t stackAdjust, MoveOp::Type result, bool callFromWasm)
{
    // Restore ra value (as stored in callWithABIPre()).
    loadPtr(Address(StackPointer, stackAdjust - sizeof(intptr_t)), ra);

    if (dynamicAlignment_) {
        // Restore sp value from stack (as stored in setupUnalignedABICall()).
        loadPtr(Address(StackPointer, stackAdjust), StackPointer);
        // Use adjustFrame instead of freeStack because we already restored sp.
        adjustFrame(-stackAdjust);
    } else {
        freeStack(stackAdjust);
    }

#ifdef DEBUG
    MOZ_ASSERT(inCall_);
    inCall_ = false;
#endif
}

void
MacroAssembler::callWithABINoProfiler(Register fun, MoveOp::Type result)
{
    // Load the callee in t9, no instruction between the lw and call
    // should clobber it. Note that we can't use fun.base because it may
    // be one of the IntArg registers clobbered before the call.
    ma_move(t9, fun);
    uint32_t stackAdjust;
    callWithABIPre(&stackAdjust);
    call(t9);
    callWithABIPost(stackAdjust, result);
}

void
MacroAssembler::callWithABINoProfiler(const Address& fun, MoveOp::Type result)
{
    // Load the callee in t9, as above.
    loadPtr(Address(fun.base, fun.offset), t9);
    uint32_t stackAdjust;
    callWithABIPre(&stackAdjust);
    call(t9);
    callWithABIPost(stackAdjust, result);
}

// ===============================================================
// Move

void
MacroAssembler::moveValue(const TypedOrValueRegister& src, const ValueOperand& dest)
{
    if (src.hasValue()) {
        moveValue(src.valueReg(), dest);
        return;
    }

    MIRType type = src.type();
    AnyRegister reg = src.typedReg();

    if (!IsFloatingPointType(type)) {
        boxNonDouble(ValueTypeFromMIRType(type), reg.gpr(), dest);
        return;
    }

    FloatRegister scratch = ScratchDoubleReg;
    FloatRegister freg = reg.fpu();
    if (type == MIRType::Float32) {
        convertFloat32ToDouble(freg, scratch);
        freg = scratch;
    }
    boxDouble(freg, dest, scratch);
}

void
MacroAssembler::moveValue(const ValueOperand& src, const ValueOperand& dest)
{
    if (src == dest)
        return;
    movePtr(src.valueReg(), dest.valueReg());
}

void
MacroAssembler::moveValue(const Value& src, const ValueOperand& dest)
{
    if(!src.isGCThing()) {
        ma_li(dest.valueReg(), ImmWord(src.asRawBits()));
        return;
    }

    writeDataRelocation(src);
    movWithPatch(ImmWord(src.asRawBits()), dest.valueReg());
}

// ===============================================================
// Branch functions

void
MacroAssembler::branchValueIsNurseryObject(Condition cond, ValueOperand value,
                                           Register temp, Label* label)
{
    MOZ_ASSERT(cond == Assembler::Equal || cond == Assembler::NotEqual);

    Label done;
    branchTestObject(Assembler::NotEqual, value, cond == Assembler::Equal ? &done : label);

    unboxObject(value, SecondScratchReg);
    orPtr(Imm32(gc::ChunkMask), SecondScratchReg);
    branch32(cond, Address(SecondScratchReg, gc::ChunkLocationOffsetFromLastByte),
             Imm32(int32_t(gc::ChunkLocation::Nursery)), label);

    bind(&done);
}

void
MacroAssembler::branchValueIsNurseryCell(Condition cond, const Address& address, Register temp,
                                         Label* label)
{
    MOZ_ASSERT(temp != InvalidReg);
    loadValue(address, ValueOperand(temp));
    branchValueIsNurseryCell(cond, ValueOperand(temp), InvalidReg, label);
}

void
MacroAssembler::branchValueIsNurseryCell(Condition cond, ValueOperand value, Register temp,
                                         Label* label)
{
    MOZ_ASSERT(cond == Assembler::Equal || cond == Assembler::NotEqual);

    Label done, checkAddress, checkObjectAddress;
    SecondScratchRegisterScope scratch2(*this);

    splitTag(value, scratch2);
    branchTestObject(Assembler::Equal, scratch2, &checkObjectAddress);
    branchTestString(Assembler::NotEqual, scratch2, cond == Assembler::Equal ? &done : label);

    unboxString(value, scratch2);
    jump(&checkAddress);

    bind(&checkObjectAddress);
    unboxObject(value, scratch2);

    bind(&checkAddress);
    orPtr(Imm32(gc::ChunkMask), scratch2);
    load32(Address(scratch2, gc::ChunkLocationOffsetFromLastByte), scratch2);
    branch32(cond, scratch2, Imm32(int32_t(gc::ChunkLocation::Nursery)), label);

    bind(&done);
}

void
MacroAssembler::branchTestValue(Condition cond, const ValueOperand& lhs,
                                const Value& rhs, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ScratchRegisterScope scratch(*this);
    MOZ_ASSERT(lhs.valueReg() != scratch);
    moveValue(rhs, ValueOperand(scratch));
    ma_b(lhs.valueReg(), scratch, label, cond);
}

// ========================================================================
// Memory access primitives.
template <typename T>
void
MacroAssembler::storeUnboxedValue(const ConstantOrRegister& value, MIRType valueType,
                                  const T& dest, MIRType slotType)
{
    if (valueType == MIRType::Double) {
        storeDouble(value.reg().typedReg().fpu(), dest);
        return;
    }

    // For known integers and booleans, we can just store the unboxed value if
    // the slot has the same type.
    if ((valueType == MIRType::Int32 || valueType == MIRType::Boolean) && slotType == valueType) {
        if (value.constant()) {
            Value val = value.value();
            if (valueType == MIRType::Int32)
                store32(Imm32(val.toInt32()), dest);
            else
                store32(Imm32(val.toBoolean() ? 1 : 0), dest);
        } else {
            store32(value.reg().typedReg().gpr(), dest);
        }
        return;
    }

    if (value.constant())
        storeValue(value.value(), dest);
    else
        storeValue(ValueTypeFromMIRType(valueType), value.reg().typedReg().gpr(), dest);
}

template void
MacroAssembler::storeUnboxedValue(const ConstantOrRegister& value, MIRType valueType,
                                  const Address& dest, MIRType slotType);
template void
MacroAssembler::storeUnboxedValue(const ConstantOrRegister& value, MIRType valueType,
                                  const BaseIndex& dest, MIRType slotType);


void
MacroAssembler::wasmBoundsCheck(Condition cond, Register index, Register boundsCheckLimit,
                                Label* label)
{
    ma_b(index, boundsCheckLimit, label, cond);
}

void
MacroAssembler::wasmBoundsCheck(Condition cond, Register index, Address boundsCheckLimit,
                                Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    load32(boundsCheckLimit, SecondScratchReg);
    ma_b(index, SecondScratchReg, label, cond);
}

void
MacroAssembler::wasmTruncateDoubleToUInt32(FloatRegister input, Register output, bool isSaturating,
                                           Label* oolEntry)
{
    as_truncld(ScratchDoubleReg, input);
    moveFromDouble(ScratchDoubleReg, output);
    ma_dsrl(ScratchRegister, output, Imm32(32));
    as_sll(output, output, 0);
    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);
}

void
MacroAssembler::wasmTruncateFloat32ToUInt32(FloatRegister input, Register output, bool isSaturating,
                                            Label* oolEntry)
{
    as_truncls(ScratchDoubleReg, input);
    moveFromDouble(ScratchDoubleReg, output);
    ma_dsrl(ScratchRegister, output, Imm32(32));
    as_sll(output, output, 0);
    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);
}

void
MacroAssembler::wasmLoadI64(const wasm::MemoryAccessDesc& access, Register memoryBase, Register ptr,
                            Register ptrScratch, Register64 output)
{
    wasmLoadI64Impl(access, memoryBase, ptr, ptrScratch, output, InvalidReg);
}

void
MacroAssembler::wasmUnalignedLoadI64(const wasm::MemoryAccessDesc& access, Register memoryBase,
                                     Register ptr, Register ptrScratch, Register64 output,
                                     Register tmp)
{
    wasmLoadI64Impl(access, memoryBase, ptr, ptrScratch, output, tmp);
}

void
MacroAssembler::wasmStoreI64(const wasm::MemoryAccessDesc& access, Register64 value,
                             Register memoryBase, Register ptr, Register ptrScratch)
{
    wasmStoreI64Impl(access, value, memoryBase, ptr, ptrScratch, InvalidReg);
}

void
MacroAssembler::wasmUnalignedStoreI64(const wasm::MemoryAccessDesc& access, Register64 value,
                                      Register memoryBase, Register ptr, Register ptrScratch,
                                      Register tmp)
{
    wasmStoreI64Impl(access, value, memoryBase, ptr, ptrScratch, tmp);
}

void
MacroAssembler::wasmTruncateDoubleToInt64(FloatRegister input, Register64 output,
                                          bool isSaturating, Label* oolEntry,
                                          Label* oolRejoin, FloatRegister tempDouble)
{
    MOZ_ASSERT(tempDouble.isInvalid());

    as_truncld(ScratchDoubleReg, input);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromDouble(ScratchDoubleReg, output.reg);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);

    if (isSaturating)
        bind(oolRejoin);
}

void
MacroAssembler::wasmTruncateDoubleToUInt64(FloatRegister input, Register64 output_,
                                           bool isSaturating, Label* oolEntry,
                                           Label* oolRejoin, FloatRegister tempDouble)
{
    MOZ_ASSERT(tempDouble.isInvalid());
    Register output = output_.reg;

    Label done;

    as_truncld(ScratchDoubleReg, input);
    // ma_li INT64_MAX
    ma_li(SecondScratchReg, Imm32(-1));
    ma_dext(SecondScratchReg, SecondScratchReg, Imm32(0), Imm32(63));
    moveFromDouble(ScratchDoubleReg, output);
    // For numbers in  -1.[ : ]INT64_MAX range do nothing more
    ma_b(output, SecondScratchReg, &done, Assembler::Below, ShortJump);

    loadConstantDouble(double(INT64_MAX + 1ULL), ScratchDoubleReg);
    // ma_li INT64_MIN
    ma_daddu(SecondScratchReg, Imm32(1));
    as_subd(ScratchDoubleReg, input, ScratchDoubleReg);
    as_truncld(ScratchDoubleReg, ScratchDoubleReg);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromDouble(ScratchDoubleReg, output);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_daddu(output, SecondScratchReg);

    // Guard against negative values that result in 0 due the precision loss.
    as_sltiu(SecondScratchReg, output, 1);
    ma_or(ScratchRegister, SecondScratchReg);

    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);

    bind(&done);

    if (isSaturating)
        bind(oolRejoin);
}

void
MacroAssembler::wasmTruncateFloat32ToInt64(FloatRegister input, Register64 output,
                                           bool isSaturating, Label* oolEntry,
                                           Label* oolRejoin, FloatRegister tempFloat)
{
    MOZ_ASSERT(tempFloat.isInvalid());

    as_truncls(ScratchDoubleReg, input);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromDouble(ScratchDoubleReg, output.reg);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);

    if (isSaturating)
        bind(oolRejoin);
}

void
MacroAssembler::wasmTruncateFloat32ToUInt64(FloatRegister input, Register64 output_,
                                            bool isSaturating, Label* oolEntry,
                                            Label* oolRejoin, FloatRegister tempFloat)
{
    MOZ_ASSERT(tempFloat.isInvalid());
    Register output = output_.reg;

    Label done;

    as_truncls(ScratchDoubleReg, input);
    // ma_li INT64_MAX
    ma_li(SecondScratchReg, Imm32(-1));
    ma_dext(SecondScratchReg, SecondScratchReg, Imm32(0), Imm32(63));
    moveFromDouble(ScratchDoubleReg, output);
    // For numbers in  -1.[ : ]INT64_MAX range do nothing more
    ma_b(output, SecondScratchReg, &done, Assembler::Below, ShortJump);

    loadConstantFloat32(float(INT64_MAX + 1ULL), ScratchFloat32Reg);
    // ma_li INT64_MIN
    ma_daddu(SecondScratchReg, Imm32(1));
    as_subs(ScratchFloat32Reg, input, ScratchFloat32Reg);
    as_truncls(ScratchDoubleReg, ScratchFloat32Reg);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromDouble(ScratchDoubleReg, output);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_daddu(output, SecondScratchReg);

    // Guard against negative values that result in 0 due the precision loss.
    as_sltiu(SecondScratchReg, output, 1);
    ma_or(ScratchRegister, SecondScratchReg);

    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);

    bind(&done);

    if (isSaturating)
        bind(oolRejoin);
}

void
MacroAssemblerPPC64LECompat::wasmLoadI64Impl(const wasm::MemoryAccessDesc& access,
                                            Register memoryBase, Register ptr, Register ptrScratch,
                                            Register64 output, Register tmp)
{
    uint32_t offset = access.offset();
    MOZ_ASSERT(offset < wasm::OffsetGuardLimit);
    MOZ_ASSERT_IF(offset, ptrScratch != InvalidReg);

    // Maybe add the offset.
    if (offset) {
        asMasm().addPtr(Imm32(offset), ptrScratch);
        ptr = ptrScratch;
    }

    unsigned byteSize = access.byteSize();
    bool isSigned;

    switch (access.type()) {
      case Scalar::Int8:   isSigned = true; break;
      case Scalar::Uint8:  isSigned = false; break;
      case Scalar::Int16:  isSigned = true; break;
      case Scalar::Uint16: isSigned = false; break;
      case Scalar::Int32:  isSigned = true; break;
      case Scalar::Uint32: isSigned = false; break;
      case Scalar::Int64:  isSigned = true; break;
      default: MOZ_CRASH("unexpected array type");
    }

    BaseIndex address(memoryBase, ptr, TimesOne);
    if (IsUnaligned(access)) {
        MOZ_ASSERT(tmp != InvalidReg);
        asMasm().ma_load_unaligned(access, output.reg, address, tmp,
                                   static_cast<LoadStoreSize>(8 * byteSize),
                                   isSigned ? SignExtend : ZeroExtend);
        return;
    }

    asMasm().memoryBarrierBefore(access.sync());
    asMasm().ma_load(output.reg, address, static_cast<LoadStoreSize>(8 * byteSize),
                     isSigned ? SignExtend : ZeroExtend);
    asMasm().append(access, asMasm().size() - 4);
    asMasm().memoryBarrierAfter(access.sync());
}

void
MacroAssemblerPPC64LECompat::wasmStoreI64Impl(const wasm::MemoryAccessDesc& access, Register64 value,
                                             Register memoryBase, Register ptr, Register ptrScratch,
                                             Register tmp)
{
    uint32_t offset = access.offset();
    MOZ_ASSERT(offset < wasm::OffsetGuardLimit);
    MOZ_ASSERT_IF(offset, ptrScratch != InvalidReg);

    // Maybe add the offset.
    if (offset) {
        asMasm().addPtr(Imm32(offset), ptrScratch);
        ptr = ptrScratch;
    }

    unsigned byteSize = access.byteSize();
    bool isSigned;
    switch (access.type()) {
      case Scalar::Int8:   isSigned = true; break;
      case Scalar::Uint8:  isSigned = false; break;
      case Scalar::Int16:  isSigned = true; break;
      case Scalar::Uint16: isSigned = false; break;
      case Scalar::Int32:  isSigned = true; break;
      case Scalar::Uint32: isSigned = false; break;
      case Scalar::Int64:  isSigned = true; break;
      default: MOZ_CRASH("unexpected array type");
    }

    BaseIndex address(memoryBase, ptr, TimesOne);

    if (IsUnaligned(access)) {
        MOZ_ASSERT(tmp != InvalidReg);
        asMasm().ma_store_unaligned(access, value.reg, address, tmp,
                                    static_cast<LoadStoreSize>(8 * byteSize),
                                    isSigned ? SignExtend : ZeroExtend);
        return;
    }

    asMasm().memoryBarrierBefore(access.sync());
    asMasm().ma_store(value.reg, address, static_cast<LoadStoreSize>(8 * byteSize),
                      isSigned ? SignExtend : ZeroExtend);
    asMasm().append(access, asMasm().size() - 4);
    asMasm().memoryBarrierAfter(access.sync());
}

template <typename T>
static void
CompareExchange64(MacroAssembler& masm, const Synchronization& sync, const T& mem,
                  Register64 expect, Register64 replace, Register64 output)
{
    masm.computeEffectiveAddress(mem, SecondScratchReg);

    Label tryAgain;
    Label exit;

    masm.memoryBarrierBefore(sync);

    masm.bind(&tryAgain);

    masm.as_lld(output.reg, SecondScratchReg, 0);
    masm.ma_b(output.reg, expect.reg, &exit, Assembler::NotEqual, ShortJump);
    masm.movePtr(replace.reg, ScratchRegister);
    masm.as_scd(ScratchRegister, SecondScratchReg, 0);
    masm.ma_b(ScratchRegister, ScratchRegister, &tryAgain, Assembler::Zero, ShortJump);

    masm.memoryBarrierAfter(sync);

    masm.bind(&exit);
}

void
MacroAssembler::compareExchange64(const Synchronization& sync, const Address& mem,
                                  Register64 expect, Register64 replace, Register64 output)
{
    CompareExchange64(*this, sync, mem, expect, replace, output);
}

void
MacroAssembler::compareExchange64(const Synchronization& sync, const BaseIndex& mem,
                                  Register64 expect, Register64 replace, Register64 output)
{
    CompareExchange64(*this, sync, mem, expect, replace, output);
}

template <typename T>
static void
AtomicExchange64(MacroAssembler& masm, const Synchronization& sync, const T& mem,
                 Register64 src, Register64 output)
{
    masm.computeEffectiveAddress(mem, SecondScratchReg);

    Label tryAgain;

    masm.memoryBarrierBefore(sync);

    masm.bind(&tryAgain);

    masm.as_lld(output.reg, SecondScratchReg, 0);
    masm.movePtr(src.reg, ScratchRegister);
    masm.as_scd(ScratchRegister, SecondScratchReg, 0);
    masm.ma_b(ScratchRegister, ScratchRegister, &tryAgain, Assembler::Zero, ShortJump);

    masm.memoryBarrierAfter(sync);
}

void
MacroAssembler::atomicExchange64(const Synchronization& sync, const Address& mem, Register64 src,
                                 Register64 output)
{
    AtomicExchange64(*this, sync, mem, src, output);
}

void
MacroAssembler::atomicExchange64(const Synchronization& sync, const BaseIndex& mem, Register64 src,
                                 Register64 output)
{
    AtomicExchange64(*this, sync, mem, src, output);
}

template<typename T>
static void
AtomicFetchOp64(MacroAssembler& masm, const Synchronization& sync, AtomicOp op, Register64 value,
                const T& mem, Register64 temp, Register64 output)
{
    masm.computeEffectiveAddress(mem, SecondScratchReg);

    Label tryAgain;

    masm.memoryBarrierBefore(sync);

    masm.bind(&tryAgain);

    masm.as_lld(output.reg, SecondScratchReg, 0);

    switch(op) {
      case AtomicFetchAddOp:
        masm.as_daddu(temp.reg, output.reg, value.reg);
        break;
      case AtomicFetchSubOp:
        masm.as_dsubu(temp.reg, output.reg, value.reg);
        break;
      case AtomicFetchAndOp:
        masm.as_and(temp.reg, output.reg, value.reg);
        break;
      case AtomicFetchOrOp:
        masm.as_or(temp.reg, output.reg, value.reg);
        break;
      case AtomicFetchXorOp:
        masm.as_xor(temp.reg, output.reg, value.reg);
        break;
      default:
        MOZ_CRASH();
    }

    masm.as_scd(temp.reg, SecondScratchReg, 0);
    masm.ma_b(temp.reg, temp.reg, &tryAgain, Assembler::Zero, ShortJump);

    masm.memoryBarrierAfter(sync);
}

void
MacroAssembler::atomicFetchOp64(const Synchronization& sync, AtomicOp op, Register64 value,
                                const Address& mem, Register64 temp, Register64 output)
{
    AtomicFetchOp64(*this, sync, op, value, mem, temp, output);
}

void
MacroAssembler::atomicFetchOp64(const Synchronization& sync, AtomicOp op, Register64 value,
                                const BaseIndex& mem, Register64 temp, Register64 output)
{
    AtomicFetchOp64(*this, sync, op, value, mem, temp, output);
}

// ========================================================================
// Convert floating point.

void
MacroAssembler::convertInt64ToDouble(Register64 src, FloatRegister dest)
{
    as_dmtc1(src.reg, dest);
    as_cvtdl(dest, dest);
}

void
MacroAssembler::convertInt64ToFloat32(Register64 src, FloatRegister dest)
{
    as_dmtc1(src.reg, dest);
    as_cvtsl(dest, dest);
}

bool
MacroAssembler::convertUInt64ToDoubleNeedsTemp()
{
    return false;
}

void
MacroAssembler::convertUInt64ToDouble(Register64 src, FloatRegister dest, Register temp)
{
    MOZ_ASSERT(temp == Register::Invalid());
    MacroAssemblerSpecific::convertUInt64ToDouble(src.reg, dest);
}

void
MacroAssembler::convertUInt64ToFloat32(Register64 src_, FloatRegister dest, Register temp)
{
    MOZ_ASSERT(temp == Register::Invalid());

    Register src = src_.reg;
    Label positive, done;
    ma_b(src, src, &positive, NotSigned, ShortJump);

    MOZ_ASSERT(src!= ScratchRegister);
    MOZ_ASSERT(src!= SecondScratchReg);

    ma_and(ScratchRegister, src, Imm32(1));
    ma_dsrl(SecondScratchReg, src, Imm32(1));
    ma_or(ScratchRegister, SecondScratchReg);
    as_dmtc1(ScratchRegister, dest);
    as_cvtsl(dest, dest);
    addFloat32(dest, dest);
    ma_b(&done, ShortJump);

    bind(&positive);
    as_dmtc1(src, dest);
    as_cvtsl(dest, dest);

    bind(&done);
}

//}}} check_macroassembler_style
/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jit/mips-shared/MacroAssembler-mips-shared.h"

#include "mozilla/EndianUtils.h"

#include "jit/MacroAssembler.h"

using namespace js;
using namespace jit;

void
MacroAssemblerMIPSShared::ma_move(Register rd, Register rs)
{
    as_or(rd, rs, zero);
}

void
MacroAssemblerMIPSShared::ma_li(Register dest, ImmGCPtr ptr)
{
    writeDataRelocation(ptr);
    asMasm().ma_liPatchable(dest, ImmPtr(ptr.value));
}

void
MacroAssemblerMIPSShared::ma_li(Register dest, Imm32 imm)
{
    if (Imm16::IsInSignedRange(imm.value)) {
        as_addiu(dest, zero, imm.value);
    } else if (Imm16::IsInUnsignedRange(imm.value)) {
        as_ori(dest, zero, Imm16::Lower(imm).encode());
    } else if (Imm16::Lower(imm).encode() == 0) {
        as_lui(dest, Imm16::Upper(imm).encode());
    } else {
        as_lui(dest, Imm16::Upper(imm).encode());
        as_ori(dest, dest, Imm16::Lower(imm).encode());
    }
}

// This method generates lui and ori instruction pair that can be modified by
// UpdateLuiOriValue, either during compilation (eg. Assembler::bind), or
// during execution (eg. jit::PatchJump).
void
MacroAssemblerMIPSShared::ma_liPatchable(Register dest, Imm32 imm)
{
    m_buffer.ensureSpace(2 * sizeof(uint32_t));
    as_lui(dest, Imm16::Upper(imm).encode());
    as_ori(dest, dest, Imm16::Lower(imm).encode());
}

// Shifts
void
MacroAssemblerMIPSShared::ma_sll(Register rd, Register rt, Imm32 shift)
{
    as_sll(rd, rt, shift.value % 32);
}
void
MacroAssemblerMIPSShared::ma_srl(Register rd, Register rt, Imm32 shift)
{
    as_srl(rd, rt, shift.value % 32);
}

void
MacroAssemblerMIPSShared::ma_sra(Register rd, Register rt, Imm32 shift)
{
    as_sra(rd, rt, shift.value % 32);
}

void
MacroAssemblerMIPSShared::ma_ror(Register rd, Register rt, Imm32 shift)
{
    if (hasR2()) {
        as_rotr(rd, rt, shift.value % 32);
    } else {
        ScratchRegisterScope scratch(asMasm());
        as_srl(scratch, rt, shift.value % 32);
        as_sll(rd, rt, (32 - (shift.value % 32)) % 32);
        as_or(rd, rd, scratch);
    }
}

void
MacroAssemblerMIPSShared::ma_rol(Register rd, Register rt, Imm32 shift)
{
    if (hasR2()) {
        as_rotr(rd, rt, (32 - (shift.value % 32)) % 32);
    } else {
        ScratchRegisterScope scratch(asMasm());
        as_srl(scratch, rt, (32 - (shift.value % 32)) % 32);
        as_sll(rd, rt, shift.value % 32);
        as_or(rd, rd, scratch);
    }
}

void
MacroAssemblerMIPSShared::ma_sll(Register rd, Register rt, Register shift)
{
    as_sllv(rd, rt, shift);
}

void
MacroAssemblerMIPSShared::ma_srl(Register rd, Register rt, Register shift)
{
    as_srlv(rd, rt, shift);
}

void
MacroAssemblerMIPSShared::ma_sra(Register rd, Register rt, Register shift)
{
    as_srav(rd, rt, shift);
}

void
MacroAssemblerMIPSShared::ma_ror(Register rd, Register rt, Register shift)
{
    if (hasR2()) {
        as_rotrv(rd, rt, shift);
    } else {
        ScratchRegisterScope scratch(asMasm());
        ma_negu(scratch, shift);
        as_sllv(scratch, rt, scratch);
        as_srlv(rd, rt, shift);
        as_or(rd, rd, scratch);
    }
}

void
MacroAssemblerMIPSShared::ma_rol(Register rd, Register rt, Register shift)
{
    ScratchRegisterScope scratch(asMasm());
    ma_negu(scratch, shift);
    if (hasR2()) {
        as_rotrv(rd, rt, scratch);
    } else {
        as_srlv(rd, rt, scratch);
        as_sllv(scratch, rt, shift);
        as_or(rd, rd, scratch);
    }
}

void
MacroAssemblerMIPSShared::ma_negu(Register rd, Register rs)
{
    as_subu(rd, zero, rs);
}

void
MacroAssemblerMIPSShared::ma_not(Register rd, Register rs)
{
    as_nor(rd, rs, zero);
}

// Bit extract/insert
void
MacroAssemblerMIPSShared::ma_ext(Register rt, Register rs, uint16_t pos, uint16_t size) {
    MOZ_ASSERT(pos < 32);
    MOZ_ASSERT(pos + size < 33);

    if (hasR2()) {
        as_ext(rt, rs, pos, size);
    } else {
        int shift_left = 32 - (pos + size);
        as_sll(rt, rs, shift_left);
        int shift_right = 32 - size;
        if (shift_right > 0) {
            as_srl(rt, rt, shift_right);
        }
    }
}

void
MacroAssemblerMIPSShared::ma_ins(Register rt, Register rs, uint16_t pos, uint16_t size) {
    MOZ_ASSERT(pos < 32);
    MOZ_ASSERT(pos + size <= 32);
    MOZ_ASSERT(size != 0);

    if (hasR2()) {
        as_ins(rt, rs, pos, size);
    } else {
        ScratchRegisterScope scratch(asMasm());
        SecondScratchRegisterScope scratch2(asMasm());
        ma_subu(scratch, zero, Imm32(1));
        as_srl(scratch, scratch, 32 - size);
        as_and(scratch2, rs, scratch);
        as_sll(scratch2, scratch2, pos);
        as_sll(scratch, scratch, pos);
        as_nor(scratch, scratch, zero);
        as_and(scratch, rt, scratch);
        as_or(rt, scratch2, scratch);
    }
}

// Sign extend
void
MacroAssemblerMIPSShared::ma_seb(Register rd, Register rt)
{
    if (hasR2()) {
        as_seb(rd, rt);
    } else {
        as_sll(rd, rt, 24);
        as_sra(rd, rd, 24);
    }
}

void
MacroAssemblerMIPSShared::ma_seh(Register rd, Register rt)
{
    if (hasR2()) {
        as_seh(rd, rt);
    } else {
        as_sll(rd, rt, 16);
        as_sra(rd, rd, 16);
    }
}

// And.
void
MacroAssemblerMIPSShared::ma_and(Register rd, Register rs)
{
    as_and(rd, rd, rs);
}

void
MacroAssemblerMIPSShared::ma_and(Register rd, Imm32 imm)
{
    ma_and(rd, rd, imm);
}

void
MacroAssemblerMIPSShared::ma_and(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInUnsignedRange(imm.value)) {
        as_andi(rd, rs, imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_and(rd, rs, ScratchRegister);
    }
}

// Or.
void
MacroAssemblerMIPSShared::ma_or(Register rd, Register rs)
{
    as_or(rd, rd, rs);
}

void
MacroAssemblerMIPSShared::ma_or(Register rd, Imm32 imm)
{
    ma_or(rd, rd, imm);
}

void
MacroAssemblerMIPSShared::ma_or(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInUnsignedRange(imm.value)) {
        as_ori(rd, rs, imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_or(rd, rs, ScratchRegister);
    }
}

// xor
void
MacroAssemblerMIPSShared::ma_xor(Register rd, Register rs)
{
    as_xor(rd, rd, rs);
}

void
MacroAssemblerMIPSShared::ma_xor(Register rd, Imm32 imm)
{
    ma_xor(rd, rd, imm);
}

void
MacroAssemblerMIPSShared::ma_xor(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInUnsignedRange(imm.value)) {
        as_xori(rd, rs, imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_xor(rd, rs, ScratchRegister);
    }
}

void
MacroAssemblerMIPSShared::ma_ctz(Register rd, Register rs)
{
    as_addiu(ScratchRegister, rs, -1);
    as_xor(rd, ScratchRegister, rs);
    as_and(rd, rd, ScratchRegister);
    as_clz(rd, rd);
    ma_li(ScratchRegister, Imm32(0x20));
    as_subu(rd, ScratchRegister, rd);
}

// Arithmetic-based ops.

// Add.
void
MacroAssemblerMIPSShared::ma_addu(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInSignedRange(imm.value)) {
        as_addiu(rd, rs, imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_addu(rd, rs, ScratchRegister);
    }
}

void
MacroAssemblerMIPSShared::ma_addu(Register rd, Register rs)
{
    as_addu(rd, rd, rs);
}

void
MacroAssemblerMIPSShared::ma_addu(Register rd, Imm32 imm)
{
    ma_addu(rd, rd, imm);
}

void
MacroAssemblerMIPSShared::ma_addTestCarry(Condition cond, Register rd, Register rs, Register rt,
                                          Label* overflow)
{
    MOZ_ASSERT(cond == Assembler::CarrySet || cond == Assembler::CarryClear);
    MOZ_ASSERT_IF(rd == rs, rt != rd);
    as_addu(rd, rs, rt);
    as_sltu(SecondScratchReg, rd, rd == rs ? rt : rs);
    ma_b(SecondScratchReg, SecondScratchReg, overflow,
         cond == Assembler::CarrySet ? Assembler::NonZero : Assembler:: Zero);
}

void
MacroAssemblerMIPSShared::ma_addTestCarry(Condition cond, Register rd, Register rs, Imm32 imm,
                                          Label* overflow)
{
    ma_li(ScratchRegister, imm);
    ma_addTestCarry(cond, rd, rs, ScratchRegister, overflow);
}

// Subtract.
void
MacroAssemblerMIPSShared::ma_subu(Register rd, Register rs, Imm32 imm)
{
    if (Imm16::IsInSignedRange(-imm.value)) {
        as_addiu(rd, rs, -imm.value);
    } else {
        ma_li(ScratchRegister, imm);
        as_subu(rd, rs, ScratchRegister);
    }
}

void
MacroAssemblerMIPSShared::ma_subu(Register rd, Imm32 imm)
{
    ma_subu(rd, rd, imm);
}

void
MacroAssemblerMIPSShared::ma_subu(Register rd, Register rs)
{
    as_subu(rd, rd, rs);
}

void
MacroAssemblerMIPSShared::ma_subTestOverflow(Register rd, Register rs, Imm32 imm, Label* overflow)
{
    if (imm.value != INT32_MIN) {
        asMasm().ma_addTestOverflow(rd, rs, Imm32(-imm.value), overflow);
    } else {
        ma_li(ScratchRegister, Imm32(imm.value));
        asMasm().ma_subTestOverflow(rd, rs, ScratchRegister, overflow);
    }
}

void
MacroAssemblerMIPSShared::ma_mul(Register rd, Register rs, Imm32 imm)
{
    ma_li(ScratchRegister, imm);
    as_mul(rd, rs, ScratchRegister);
}

void
MacroAssemblerMIPSShared::ma_mul_branch_overflow(Register rd, Register rs, Register rt, Label* overflow)
{
    as_mult(rs, rt);
    as_mflo(rd);
    as_sra(ScratchRegister, rd, 31);
    as_mfhi(SecondScratchReg);
    ma_b(ScratchRegister, SecondScratchReg, overflow, Assembler::NotEqual);
}

void
MacroAssemblerMIPSShared::ma_mul_branch_overflow(Register rd, Register rs, Imm32 imm, Label* overflow)
{
    ma_li(ScratchRegister, imm);
    ma_mul_branch_overflow(rd, rs, ScratchRegister, overflow);
}

void
MacroAssemblerMIPSShared::ma_div_branch_overflow(Register rd, Register rs, Register rt, Label* overflow)
{
    as_div(rs, rt);
    as_mfhi(ScratchRegister);
    ma_b(ScratchRegister, ScratchRegister, overflow, Assembler::NonZero);
    as_mflo(rd);
}

void
MacroAssemblerMIPSShared::ma_div_branch_overflow(Register rd, Register rs, Imm32 imm, Label* overflow)
{
    ma_li(ScratchRegister, imm);
    ma_div_branch_overflow(rd, rs, ScratchRegister, overflow);
}

void
MacroAssemblerMIPSShared::ma_mod_mask(Register src, Register dest, Register hold, Register remain,
                                      int32_t shift, Label* negZero)
{
    // MATH:
    // We wish to compute x % (1<<y) - 1 for a known constant, y.
    // First, let b = (1<<y) and C = (1<<y)-1, then think of the 32 bit
    // dividend as a number in base b, namely
    // c_0*1 + c_1*b + c_2*b^2 ... c_n*b^n
    // now, since both addition and multiplication commute with modulus,
    // x % C == (c_0 + c_1*b + ... + c_n*b^n) % C ==
    // (c_0 % C) + (c_1%C) * (b % C) + (c_2 % C) * (b^2 % C)...
    // now, since b == C + 1, b % C == 1, and b^n % C == 1
    // this means that the whole thing simplifies to:
    // c_0 + c_1 + c_2 ... c_n % C
    // each c_n can easily be computed by a shift/bitextract, and the modulus
    // can be maintained by simply subtracting by C whenever the number gets
    // over C.
    int32_t mask = (1 << shift) - 1;
    Label head, negative, sumSigned, done;

    // hold holds -1 if the value was negative, 1 otherwise.
    // remain holds the remaining bits that have not been processed
    // SecondScratchReg serves as a temporary location to store extracted bits
    // into as well as holding the trial subtraction as a temp value dest is
    // the accumulator (and holds the final result)

    // move the whole value into the remain.
    ma_move(remain, src);
    // Zero out the dest.
    ma_li(dest, Imm32(0));
    // Set the hold appropriately.
    ma_b(remain, remain, &negative, Signed, ShortJump);
    ma_li(hold, Imm32(1));
    ma_b(&head, ShortJump);

    bind(&negative);
    ma_li(hold, Imm32(-1));
    ma_negu(remain, remain);

    // Begin the main loop.
    bind(&head);

    // Extract the bottom bits into SecondScratchReg.
    ma_and(SecondScratchReg, remain, Imm32(mask));
    // Add those bits to the accumulator.
    as_addu(dest, dest, SecondScratchReg);
    // Do a trial subtraction
    ma_subu(SecondScratchReg, dest, Imm32(mask));
    // If (sum - C) > 0, store sum - C back into sum, thus performing a
    // modulus.
    ma_b(SecondScratchReg, SecondScratchReg, &sumSigned, Signed, ShortJump);
    ma_move(dest, SecondScratchReg);
    bind(&sumSigned);
    // Get rid of the bits that we extracted before.
    as_srl(remain, remain, shift);
    // If the shift produced zero, finish, otherwise, continue in the loop.
    ma_b(remain, remain, &head, NonZero, ShortJump);
    // Check the hold to see if we need to negate the result.
    ma_b(hold, hold, &done, NotSigned, ShortJump);

    // If the hold was non-zero, negate the result to be in line with
    // what JS wants
    if (negZero != nullptr) {
        // Jump out in case of negative zero.
        ma_b(hold, hold, negZero, Zero);
        ma_negu(dest, dest);
    } else {
        ma_negu(dest, dest);
    }

    bind(&done);
}

// Memory.

void
MacroAssemblerMIPSShared::ma_load(Register dest, const BaseIndex& src,
                                  LoadStoreSize size, LoadStoreExtension extension)
{
    if (isLoongson() && ZeroExtend != extension && Imm8::IsInSignedRange(src.offset)) {
        Register index = src.index;

        if (src.scale != TimesOne) {
            int32_t shift = Imm32::ShiftOf(src.scale).value;

            MOZ_ASSERT(SecondScratchReg != src.base);
            index = SecondScratchReg;
#ifdef JS_CODEGEN_PPC64LE
            asMasm().ma_dsll(index, src.index, Imm32(shift));
#else
            asMasm().ma_sll(index, src.index, Imm32(shift));
#endif
        }

        switch (size) {
          case SizeByte:
            as_gslbx(dest, src.base, index, src.offset);
            break;
          case SizeHalfWord:
            as_gslhx(dest, src.base, index, src.offset);
            break;
          case SizeWord:
            as_gslwx(dest, src.base, index, src.offset);
            break;
          case SizeDouble:
            as_gsldx(dest, src.base, index, src.offset);
            break;
          default:
            MOZ_CRASH("Invalid argument for ma_load");
        }
        return;
    }

    asMasm().computeScaledAddress(src, SecondScratchReg);
    asMasm().ma_load(dest, Address(SecondScratchReg, src.offset), size, extension);
}

void
MacroAssemblerMIPSShared::ma_load_unaligned(const wasm::MemoryAccessDesc& access, Register dest, const BaseIndex& src, Register temp,
                                            LoadStoreSize size, LoadStoreExtension extension)
{
    MOZ_ASSERT(MOZ_LITTLE_ENDIAN, "Wasm-only; wasm is disabled on big-endian.");
    int16_t lowOffset, hiOffset;
    Register base;

    asMasm().computeScaledAddress(src, SecondScratchReg);

    if (Imm16::IsInSignedRange(src.offset) && Imm16::IsInSignedRange(src.offset + size / 8 - 1)) {
        base = SecondScratchReg;
        lowOffset = Imm16(src.offset).encode();
        hiOffset = Imm16(src.offset + size / 8 - 1).encode();
    } else {
        ma_li(ScratchRegister, Imm32(src.offset));
        asMasm().addPtr(SecondScratchReg, ScratchRegister);
        base = ScratchRegister;
        lowOffset = Imm16(0).encode();
        hiOffset = Imm16(size / 8 - 1).encode();
    }

    BufferOffset load;
    switch (size) {
      case SizeHalfWord:
        if (extension != ZeroExtend)
            load = as_lbu(temp, base, hiOffset);
        else
            load = as_lb(temp, base, hiOffset);
        as_lbu(dest, base, lowOffset);
        ma_ins(dest, temp, 8, 24);
        break;
      case SizeWord:
        load = as_lwl(dest, base, hiOffset);
        as_lwr(dest, base, lowOffset);
#ifdef JS_CODEGEN_PPC64LE
        if (extension != ZeroExtend)
            as_dext(dest, dest, 0, 32);
#endif
        break;
#ifdef JS_CODEGEN_PPC64LE
      case SizeDouble:
        load = as_ldl(dest, base, hiOffset);
        as_ldr(dest, base, lowOffset);
        break;
#endif
      default:
        MOZ_CRASH("Invalid argument for ma_load");
    }

    append(access, load.getOffset());
}

void
MacroAssemblerMIPSShared::ma_store(Register data, const BaseIndex& dest,
                                   LoadStoreSize size, LoadStoreExtension extension)
{
    if (isLoongson() && Imm8::IsInSignedRange(dest.offset)) {
        Register index = dest.index;

        if (dest.scale != TimesOne) {
            int32_t shift = Imm32::ShiftOf(dest.scale).value;

            MOZ_ASSERT(SecondScratchReg != dest.base);
            index = SecondScratchReg;
#ifdef JS_CODEGEN_PPC64LE
            asMasm().ma_dsll(index, dest.index, Imm32(shift));
#else
            asMasm().ma_sll(index, dest.index, Imm32(shift));
#endif
        }

        switch (size) {
          case SizeByte:
            as_gssbx(data, dest.base, index, dest.offset);
            break;
          case SizeHalfWord:
            as_gsshx(data, dest.base, index, dest.offset);
            break;
          case SizeWord:
            as_gsswx(data, dest.base, index, dest.offset);
            break;
          case SizeDouble:
            as_gssdx(data, dest.base, index, dest.offset);
            break;
          default:
            MOZ_CRASH("Invalid argument for ma_store");
        }
        return;
    }

    asMasm().computeScaledAddress(dest, SecondScratchReg);
    asMasm().ma_store(data, Address(SecondScratchReg, dest.offset), size, extension);
}

void
MacroAssemblerMIPSShared::ma_store(Imm32 imm, const BaseIndex& dest,
                                   LoadStoreSize size, LoadStoreExtension extension)
{
    if (isLoongson() && Imm8::IsInSignedRange(dest.offset)) {
        Register data = zero;
        Register index = dest.index;

        if (imm.value) {
            MOZ_ASSERT(ScratchRegister != dest.base);
            MOZ_ASSERT(ScratchRegister != dest.index);
            data = ScratchRegister;
            ma_li(data, imm);
        }

        if (dest.scale != TimesOne) {
            int32_t shift = Imm32::ShiftOf(dest.scale).value;

            MOZ_ASSERT(SecondScratchReg != dest.base);
            index = SecondScratchReg;
#ifdef JS_CODEGEN_PPC64LE
            asMasm().ma_dsll(index, dest.index, Imm32(shift));
#else
            asMasm().ma_sll(index, dest.index, Imm32(shift));
#endif
        }

        switch (size) {
          case SizeByte:
            as_gssbx(data, dest.base, index, dest.offset);
            break;
          case SizeHalfWord:
            as_gsshx(data, dest.base, index, dest.offset);
            break;
          case SizeWord:
            as_gsswx(data, dest.base, index, dest.offset);
            break;
          case SizeDouble:
            as_gssdx(data, dest.base, index, dest.offset);
            break;
          default:
            MOZ_CRASH("Invalid argument for ma_store");
        }
        return;
    }

    // Make sure that SecondScratchReg contains absolute address so that
    // offset is 0.
    asMasm().computeEffectiveAddress(dest, SecondScratchReg);

    // Scrach register is free now, use it for loading imm value
    ma_li(ScratchRegister, imm);

    // with offset=0 ScratchRegister will not be used in ma_store()
    // so we can use it as a parameter here
    asMasm().ma_store(ScratchRegister, Address(SecondScratchReg, 0), size, extension);
}

void
MacroAssemblerMIPSShared::ma_store_unaligned(const wasm::MemoryAccessDesc& access, Register data,
                                             const BaseIndex& dest, Register temp,
                                             LoadStoreSize size, LoadStoreExtension extension)
{
    MOZ_ASSERT(MOZ_LITTLE_ENDIAN, "Wasm-only; wasm is disabled on big-endian.");
    int16_t lowOffset, hiOffset;
    Register base;

    asMasm().computeScaledAddress(dest, SecondScratchReg);

    if (Imm16::IsInSignedRange(dest.offset) && Imm16::IsInSignedRange(dest.offset + size / 8 - 1)) {
        base = SecondScratchReg;
        lowOffset = Imm16(dest.offset).encode();
        hiOffset = Imm16(dest.offset + size / 8 - 1).encode();
    } else {
        ma_li(ScratchRegister, Imm32(dest.offset));
        asMasm().addPtr(SecondScratchReg, ScratchRegister);
        base = ScratchRegister;
        lowOffset = Imm16(0).encode();
        hiOffset = Imm16(size / 8 - 1).encode();
    }

    BufferOffset store;
    switch (size) {
      case SizeHalfWord:
        ma_ext(temp, data, 8, 8);
        store = as_sb(temp, base, hiOffset);
        as_sb(data, base, lowOffset);
        break;
      case SizeWord:
        store = as_swl(data, base, hiOffset);
        as_swr(data, base, lowOffset);
        break;
#ifdef JS_CODEGEN_PPC64LE
      case SizeDouble:
        store = as_sdl(data, base, hiOffset);
        as_sdr(data, base, lowOffset);
        break;
#endif
      default:
        MOZ_CRASH("Invalid argument for ma_store");
    }
    append(access, store.getOffset());
}

// Branches when done from within mips-specific code.
void
MacroAssemblerMIPSShared::ma_b(Register lhs, Register rhs, Label* label, Condition c, JumpKind jumpKind)
{
    switch (c) {
      case Equal :
      case NotEqual:
        asMasm().branchWithCode(getBranchCode(lhs, rhs, c), label, jumpKind);
        break;
      case Always:
        ma_b(label, jumpKind);
        break;
      case Zero:
      case NonZero:
      case Signed:
      case NotSigned:
        MOZ_ASSERT(lhs == rhs);
        asMasm().branchWithCode(getBranchCode(lhs, c), label, jumpKind);
        break;
      default:
        Condition cond = ma_cmp(ScratchRegister, lhs, rhs, c);
        asMasm().branchWithCode(getBranchCode(ScratchRegister, cond), label, jumpKind);
        break;
    }
}

void
MacroAssemblerMIPSShared::ma_b(Register lhs, Imm32 imm, Label* label, Condition c, JumpKind jumpKind)
{
    MOZ_ASSERT(c != Overflow);
    if (imm.value == 0) {
        if (c == Always || c == AboveOrEqual)
            ma_b(label, jumpKind);
        else if (c == Below)
            ; // This condition is always false. No branch required.
        else
            asMasm().branchWithCode(getBranchCode(lhs, c), label, jumpKind);
    } else {
      switch (c) {
        case Equal:
        case NotEqual:
          MOZ_ASSERT(lhs != ScratchRegister);
          ma_li(ScratchRegister, imm);
          ma_b(lhs, ScratchRegister, label, c, jumpKind);
          break;
        default:
          Condition cond = ma_cmp(ScratchRegister, lhs, imm, c);
          asMasm().branchWithCode(getBranchCode(ScratchRegister, cond), label, jumpKind);
        }
    }
}

void
MacroAssemblerMIPSShared::ma_b(Register lhs, ImmPtr imm, Label* l, Condition c, JumpKind jumpKind)
{
    asMasm().ma_b(lhs, ImmWord(uintptr_t(imm.value)), l, c, jumpKind);
}

void
MacroAssemblerMIPSShared::ma_b(Label* label, JumpKind jumpKind)
{
    asMasm().branchWithCode(getBranchCode(BranchIsJump), label, jumpKind);
}

Assembler::Condition
MacroAssemblerMIPSShared::ma_cmp(Register scratch, Register lhs, Register rhs, Condition c)
{
    switch (c) {
      case Above:
        // bgtu s,t,label =>
        //   sltu at,t,s
        //   bne at,$zero,offs
        as_sltu(scratch, rhs, lhs);
        return NotEqual;
      case AboveOrEqual:
        // bgeu s,t,label =>
        //   sltu at,s,t
        //   beq at,$zero,offs
        as_sltu(scratch, lhs, rhs);
        return Equal;
      case Below:
        // bltu s,t,label =>
        //   sltu at,s,t
        //   bne at,$zero,offs
        as_sltu(scratch, lhs, rhs);
        return NotEqual;
      case BelowOrEqual:
        // bleu s,t,label =>
        //   sltu at,t,s
        //   beq at,$zero,offs
        as_sltu(scratch, rhs, lhs);
        return Equal;
      case GreaterThan:
        // bgt s,t,label =>
        //   slt at,t,s
        //   bne at,$zero,offs
        as_slt(scratch, rhs, lhs);
        return NotEqual;
      case GreaterThanOrEqual:
        // bge s,t,label =>
        //   slt at,s,t
        //   beq at,$zero,offs
        as_slt(scratch, lhs, rhs);
        return Equal;
      case LessThan:
        // blt s,t,label =>
        //   slt at,s,t
        //   bne at,$zero,offs
        as_slt(scratch, lhs, rhs);
        return NotEqual;
      case LessThanOrEqual:
        // ble s,t,label =>
        //   slt at,t,s
        //   beq at,$zero,offs
        as_slt(scratch, rhs, lhs);
        return Equal;
      default:
        MOZ_CRASH("Invalid condition.");
    }
    return Always;
}

Assembler::Condition
MacroAssemblerMIPSShared::ma_cmp(Register scratch, Register lhs, Imm32 imm, Condition c)
{
    switch (c) {
      case Above:
      case BelowOrEqual:
        if (Imm16::IsInSignedRange(imm.value + 1) && imm.value != -1) {
          // lhs <= rhs via lhs < rhs + 1 if rhs + 1 does not overflow
          as_sltiu(scratch, lhs, imm.value + 1);

          return (c == BelowOrEqual ? NotEqual : Equal);
        } else {
          ma_li(scratch, imm);
          as_sltu(scratch, scratch, lhs);
          return (c == BelowOrEqual ? Equal : NotEqual);
        }
      case AboveOrEqual:
      case Below:
        if (Imm16::IsInSignedRange(imm.value)) {
          as_sltiu(scratch, lhs, imm.value);
        } else {
          ma_li(scratch, imm);
          as_sltu(scratch, lhs, scratch);
        }
        return (c == AboveOrEqual ? Equal : NotEqual);
      case GreaterThan:
      case LessThanOrEqual:
        if (Imm16::IsInSignedRange(imm.value + 1)) {
          // lhs <= rhs via lhs < rhs + 1.
          as_slti(scratch, lhs, imm.value + 1);
          return (c == LessThanOrEqual ? NotEqual : Equal);
        } else {
          ma_li(scratch, imm);
          as_slt(scratch, scratch, lhs);
          return (c == LessThanOrEqual ? Equal : NotEqual);
        }
      case GreaterThanOrEqual:
      case LessThan:
        if (Imm16::IsInSignedRange(imm.value)) {
          as_slti(scratch, lhs, imm.value);
        } else {
          ma_li(scratch, imm);
          as_slt(scratch, lhs, scratch);
        }
        return (c == GreaterThanOrEqual ? Equal : NotEqual);
      default:
        MOZ_CRASH("Invalid condition.");
    }
    return Always;
}

void
MacroAssemblerMIPSShared::ma_cmp_set(Register rd, Register rs, Register rt, Condition c)
{
    switch (c) {
      case Equal :
        // seq d,s,t =>
        //   xor d,s,t
        //   sltiu d,d,1
        as_xor(rd, rs, rt);
        as_sltiu(rd, rd, 1);
        break;
      case NotEqual:
        // sne d,s,t =>
        //   xor d,s,t
        //   sltu d,$zero,d
        as_xor(rd, rs, rt);
        as_sltu(rd, zero, rd);
        break;
      case Above:
        // sgtu d,s,t =>
        //   sltu d,t,s
        as_sltu(rd, rt, rs);
        break;
      case AboveOrEqual:
        // sgeu d,s,t =>
        //   sltu d,s,t
        //   xori d,d,1
        as_sltu(rd, rs, rt);
        as_xori(rd, rd, 1);
        break;
      case Below:
        // sltu d,s,t
        as_sltu(rd, rs, rt);
        break;
      case BelowOrEqual:
        // sleu d,s,t =>
        //   sltu d,t,s
        //   xori d,d,1
        as_sltu(rd, rt, rs);
        as_xori(rd, rd, 1);
        break;
      case GreaterThan:
        // sgt d,s,t =>
        //   slt d,t,s
        as_slt(rd, rt, rs);
        break;
      case GreaterThanOrEqual:
        // sge d,s,t =>
        //   slt d,s,t
        //   xori d,d,1
        as_slt(rd, rs, rt);
        as_xori(rd, rd, 1);
        break;
      case LessThan:
        // slt d,s,t
        as_slt(rd, rs, rt);
        break;
      case LessThanOrEqual:
        // sle d,s,t =>
        //   slt d,t,s
        //   xori d,d,1
        as_slt(rd, rt, rs);
        as_xori(rd, rd, 1);
        break;
      case Zero:
        MOZ_ASSERT(rs == rt);
        // seq d,s,$zero =>
        //   sltiu d,s,1
        as_sltiu(rd, rs, 1);
        break;
      case NonZero:
        MOZ_ASSERT(rs == rt);
        // sne d,s,$zero =>
        //   sltu d,$zero,s
        as_sltu(rd, zero, rs);
        break;
      case Signed:
        MOZ_ASSERT(rs == rt);
        as_slt(rd, rs, zero);
        break;
      case NotSigned:
        MOZ_ASSERT(rs == rt);
        // sge d,s,$zero =>
        //   slt d,s,$zero
        //   xori d,d,1
        as_slt(rd, rs, zero);
        as_xori(rd, rd, 1);
        break;
      default:
        MOZ_CRASH("Invalid condition.");
    }
}

void
MacroAssemblerMIPSShared::compareFloatingPoint(FloatFormat fmt, FloatRegister lhs, FloatRegister rhs,
                                               DoubleCondition c, FloatTestKind* testKind,
                                               FPConditionBit fcc)
{
    switch (c) {
      case DoubleOrdered:
        as_cun(fmt, lhs, rhs, fcc);
        *testKind = TestForFalse;
        break;
      case DoubleEqual:
        as_ceq(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleNotEqual:
        as_cueq(fmt, lhs, rhs, fcc);
        *testKind = TestForFalse;
        break;
      case DoubleGreaterThan:
        as_colt(fmt, rhs, lhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleGreaterThanOrEqual:
        as_cole(fmt, rhs, lhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleLessThan:
        as_colt(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleLessThanOrEqual:
        as_cole(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleUnordered:
        as_cun(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleEqualOrUnordered:
        as_cueq(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleNotEqualOrUnordered:
        as_ceq(fmt, lhs, rhs, fcc);
        *testKind = TestForFalse;
        break;
      case DoubleGreaterThanOrUnordered:
        as_cult(fmt, rhs, lhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleGreaterThanOrEqualOrUnordered:
        as_cule(fmt, rhs, lhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleLessThanOrUnordered:
        as_cult(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      case DoubleLessThanOrEqualOrUnordered:
        as_cule(fmt, lhs, rhs, fcc);
        *testKind = TestForTrue;
        break;
      default:
        MOZ_CRASH("Invalid DoubleCondition.");
    }
}

void
MacroAssemblerMIPSShared::ma_cmp_set_double(Register dest, FloatRegister lhs, FloatRegister rhs,
                                            DoubleCondition c)
{
    FloatTestKind moveCondition;
    compareFloatingPoint(DoubleFloat, lhs, rhs, c, &moveCondition);

    ma_li(dest, Imm32(1));

    if (moveCondition == TestForTrue)
        as_movf(dest, zero);
    else
        as_movt(dest, zero);
}

void
MacroAssemblerMIPSShared::ma_cmp_set_float32(Register dest, FloatRegister lhs, FloatRegister rhs,
                                             DoubleCondition c)
{
    FloatTestKind moveCondition;
    compareFloatingPoint(SingleFloat, lhs, rhs, c, &moveCondition);

    ma_li(dest, Imm32(1));

    if (moveCondition == TestForTrue)
        as_movf(dest, zero);
    else
        as_movt(dest, zero);
}

void
MacroAssemblerMIPSShared::ma_cmp_set(Register rd, Register rs, Imm32 imm, Condition c)
{
    if (imm.value == 0) {
        switch (c) {
          case Equal :
          case BelowOrEqual:
            as_sltiu(rd, rs, 1);
            break;
          case NotEqual:
          case Above:
            as_sltu(rd, zero, rs);
            break;
          case AboveOrEqual:
          case Below:
            as_ori(rd, zero, c == AboveOrEqual ? 1: 0);
            break;
          case GreaterThan:
          case LessThanOrEqual:
            as_slt(rd, zero, rs);
            if (c == LessThanOrEqual)
                as_xori(rd, rd, 1);
            break;
          case LessThan:
          case GreaterThanOrEqual:
            as_slt(rd, rs, zero);
            if (c == GreaterThanOrEqual)
                as_xori(rd, rd, 1);
            break;
          case Zero:
            as_sltiu(rd, rs, 1);
            break;
          case NonZero:
            as_sltu(rd, zero, rs);
            break;
          case Signed:
            as_slt(rd, rs, zero);
            break;
          case NotSigned:
            as_slt(rd, rs, zero);
            as_xori(rd, rd, 1);
            break;
          default:
            MOZ_CRASH("Invalid condition.");
        }
        return;
    }

    switch (c) {
      case Equal:
      case NotEqual:
        MOZ_ASSERT(rs != ScratchRegister);
        ma_xor(rd, rs, imm);
        if (c == Equal)
            as_sltiu(rd, rd, 1);
        else
            as_sltu(rd, zero, rd);
        break;
      case Zero:
      case NonZero:
      case Signed:
      case NotSigned:
        MOZ_CRASH("Invalid condition.");
      default:
        Condition cond = ma_cmp(rd, rs, imm, c);
        MOZ_ASSERT(cond == Equal || cond == NotEqual);

        if(cond == Equal)
            as_xori(rd, rd, 1);
    }
}

// fp instructions
void
MacroAssemblerMIPSShared::ma_lis(FloatRegister dest, float value)
{
    Imm32 imm(mozilla::BitwiseCast<uint32_t>(value));

    if(imm.value != 0) {
        ma_li(ScratchRegister, imm);
        moveToFloat32(ScratchRegister, dest);
    } else {
        moveToFloat32(zero, dest);
    }
}

void
MacroAssemblerMIPSShared::ma_sd(FloatRegister ft, BaseIndex address)
{
    if (isLoongson() && Imm8::IsInSignedRange(address.offset)) {
        Register index = address.index;

        if (address.scale != TimesOne) {
            int32_t shift = Imm32::ShiftOf(address.scale).value;

            MOZ_ASSERT(SecondScratchReg != address.base);
            index = SecondScratchReg;
#ifdef JS_CODEGEN_PPC64LE
            asMasm().ma_dsll(index, address.index, Imm32(shift));
#else
            asMasm().ma_sll(index, address.index, Imm32(shift));
#endif
        }

        as_gssdx(ft, address.base, index, address.offset);
        return;
    }

    asMasm().computeScaledAddress(address, SecondScratchReg);
    asMasm().ma_sd(ft, Address(SecondScratchReg, address.offset));
}

void
MacroAssemblerMIPSShared::ma_ss(FloatRegister ft, BaseIndex address)
{
    if (isLoongson() && Imm8::IsInSignedRange(address.offset)) {
        Register index = address.index;

        if (address.scale != TimesOne) {
            int32_t shift = Imm32::ShiftOf(address.scale).value;

            MOZ_ASSERT(SecondScratchReg != address.base);
            index = SecondScratchReg;
#ifdef JS_CODEGEN_PPC64LE
            asMasm().ma_dsll(index, address.index, Imm32(shift));
#else
            asMasm().ma_sll(index, address.index, Imm32(shift));
#endif
        }

        as_gsssx(ft, address.base, index, address.offset);
        return;
    }

    asMasm().computeScaledAddress(address, SecondScratchReg);
    asMasm().ma_ss(ft, Address(SecondScratchReg, address.offset));
}

void
MacroAssemblerMIPSShared::ma_ld(FloatRegister ft, const BaseIndex& src)
{
    asMasm().computeScaledAddress(src, SecondScratchReg);
    asMasm().ma_ld(ft, Address(SecondScratchReg, src.offset));
}

void
MacroAssemblerMIPSShared::ma_ls(FloatRegister ft, const BaseIndex& src)
{
    asMasm().computeScaledAddress(src, SecondScratchReg);
    asMasm().ma_ls(ft, Address(SecondScratchReg, src.offset));
}

void
MacroAssemblerMIPSShared::ma_bc1s(FloatRegister lhs, FloatRegister rhs, Label* label,
                                  DoubleCondition c, JumpKind jumpKind, FPConditionBit fcc)
{
    FloatTestKind testKind;
    compareFloatingPoint(SingleFloat, lhs, rhs, c, &testKind, fcc);
    asMasm().branchWithCode(getBranchCode(testKind, fcc), label, jumpKind);
}

void
MacroAssemblerMIPSShared::ma_bc1d(FloatRegister lhs, FloatRegister rhs, Label* label,
                                  DoubleCondition c, JumpKind jumpKind, FPConditionBit fcc)
{
    FloatTestKind testKind;
    compareFloatingPoint(DoubleFloat, lhs, rhs, c, &testKind, fcc);
    asMasm().branchWithCode(getBranchCode(testKind, fcc), label, jumpKind);
}

void
MacroAssemblerMIPSShared::minMaxDouble(FloatRegister srcDest, FloatRegister second,
                                       bool handleNaN, bool isMax)
{
    FloatRegister first = srcDest;

    Assembler::DoubleCondition cond = isMax
                                      ? Assembler::DoubleLessThanOrEqual
                                      : Assembler::DoubleGreaterThanOrEqual;
    Label nan, equal, done;
    FloatTestKind moveCondition;

    // First or second is NaN, result is NaN.
    ma_bc1d(first, second, &nan, Assembler::DoubleUnordered, ShortJump);
    // Make sure we handle -0 and 0 right.
    ma_bc1d(first, second, &equal, Assembler::DoubleEqual, ShortJump);
    compareFloatingPoint(DoubleFloat, first, second, cond, &moveCondition);
    MOZ_ASSERT(TestForTrue == moveCondition);
    as_movt(DoubleFloat, first, second);
    ma_b(&done, ShortJump);

    // Check for zero.
    bind(&equal);
    asMasm().loadConstantDouble(0.0, ScratchDoubleReg);
    compareFloatingPoint(DoubleFloat, first, ScratchDoubleReg,
                         Assembler::DoubleEqual, &moveCondition);

    // So now both operands are either -0 or 0.
    if (isMax) {
        // -0 + -0 = -0 and -0 + 0 = 0.
        as_addd(ScratchDoubleReg, first, second);
    } else {
        as_negd(ScratchDoubleReg, first);
        as_subd(ScratchDoubleReg, ScratchDoubleReg, second);
        as_negd(ScratchDoubleReg, ScratchDoubleReg);
    }
    MOZ_ASSERT(TestForTrue == moveCondition);
    // First is 0 or -0, move max/min to it, else just return it.
    as_movt(DoubleFloat, first, ScratchDoubleReg);
    ma_b(&done, ShortJump);

    bind(&nan);
    asMasm().loadConstantDouble(JS::GenericNaN(), srcDest);

    bind(&done);
}

void
MacroAssemblerMIPSShared::minMaxFloat32(FloatRegister srcDest, FloatRegister second,
                                        bool handleNaN, bool isMax)
{
    FloatRegister first = srcDest;

    Assembler::DoubleCondition cond = isMax
                                      ? Assembler::DoubleLessThanOrEqual
                                      : Assembler::DoubleGreaterThanOrEqual;
    Label nan, equal, done;
    FloatTestKind moveCondition;

    // First or second is NaN, result is NaN.
    ma_bc1s(first, second, &nan, Assembler::DoubleUnordered, ShortJump);
    // Make sure we handle -0 and 0 right.
    ma_bc1s(first, second, &equal, Assembler::DoubleEqual, ShortJump);
    compareFloatingPoint(SingleFloat, first, second, cond, &moveCondition);
    MOZ_ASSERT(TestForTrue == moveCondition);
    as_movt(SingleFloat, first, second);
    ma_b(&done, ShortJump);

    // Check for zero.
    bind(&equal);
    asMasm().loadConstantFloat32(0.0f, ScratchFloat32Reg);
    compareFloatingPoint(SingleFloat, first, ScratchFloat32Reg,
                         Assembler::DoubleEqual, &moveCondition);

    // So now both operands are either -0 or 0.
    if (isMax) {
        // -0 + -0 = -0 and -0 + 0 = 0.
        as_adds(ScratchFloat32Reg, first, second);
    } else {
        as_negs(ScratchFloat32Reg, first);
        as_subs(ScratchFloat32Reg, ScratchFloat32Reg, second);
        as_negs(ScratchFloat32Reg, ScratchFloat32Reg);
    }
    MOZ_ASSERT(TestForTrue == moveCondition);
    // First is 0 or -0, move max/min to it, else just return it.
    as_movt(SingleFloat, first, ScratchFloat32Reg);
    ma_b(&done, ShortJump);

    bind(&nan);
    asMasm().loadConstantFloat32(JS::GenericNaN(), srcDest);

    bind(&done);
}

void
MacroAssemblerMIPSShared::loadDouble(const Address& address, FloatRegister dest)
{
    asMasm().ma_ld(dest, address);
}

void
MacroAssemblerMIPSShared::loadDouble(const BaseIndex& src, FloatRegister dest)
{
    asMasm().ma_ld(dest, src);
}

void
MacroAssemblerMIPSShared::loadFloatAsDouble(const Address& address, FloatRegister dest)
{
    asMasm().ma_ls(dest, address);
    as_cvtds(dest, dest);
}

void
MacroAssemblerMIPSShared::loadFloatAsDouble(const BaseIndex& src, FloatRegister dest)
{
    asMasm().loadFloat32(src, dest);
    as_cvtds(dest, dest);
}

void
MacroAssemblerMIPSShared::loadFloat32(const Address& address, FloatRegister dest)
{
    asMasm().ma_ls(dest, address);
}

void
MacroAssemblerMIPSShared::loadFloat32(const BaseIndex& src, FloatRegister dest)
{
    asMasm().ma_ls(dest, src);
}

void
MacroAssemblerMIPSShared::ma_call(ImmPtr dest)
{
    asMasm().ma_liPatchable(CallReg, dest);
    as_jalr(CallReg);
    as_nop();
}

void
MacroAssemblerMIPSShared::ma_jump(ImmPtr dest)
{
    asMasm().ma_liPatchable(ScratchRegister, dest);
    as_jr(ScratchRegister);
    as_nop();
}

MacroAssembler&
MacroAssemblerMIPSShared::asMasm()
{
    return *static_cast<MacroAssembler*>(this);
}

const MacroAssembler&
MacroAssemblerMIPSShared::asMasm() const
{
    return *static_cast<const MacroAssembler*>(this);
}

//{{{ check_macroassembler_style
// ===============================================================
// MacroAssembler high-level usage.

void
MacroAssembler::flush()
{
}

// ===============================================================
// Stack manipulation functions.

void
MacroAssembler::Push(Register reg)
{
    ma_push(reg);
    adjustFrame(int32_t(sizeof(intptr_t)));
}

void
MacroAssembler::Push(const Imm32 imm)
{
    ma_li(ScratchRegister, imm);
    ma_push(ScratchRegister);
    adjustFrame(int32_t(sizeof(intptr_t)));
}

void
MacroAssembler::Push(const ImmWord imm)
{
    ma_li(ScratchRegister, imm);
    ma_push(ScratchRegister);
    adjustFrame(int32_t(sizeof(intptr_t)));
}

void
MacroAssembler::Push(const ImmPtr imm)
{
    Push(ImmWord(uintptr_t(imm.value)));
}

void
MacroAssembler::Push(const ImmGCPtr ptr)
{
    ma_li(ScratchRegister, ptr);
    ma_push(ScratchRegister);
    adjustFrame(int32_t(sizeof(intptr_t)));
}

void
MacroAssembler::Push(FloatRegister f)
{
    ma_push(f);
    adjustFrame(int32_t(f.pushSize()));
}

void
MacroAssembler::Pop(Register reg)
{
    ma_pop(reg);
    adjustFrame(-int32_t(sizeof(intptr_t)));
}

void
MacroAssembler::Pop(FloatRegister f)
{
    ma_pop(f);
    adjustFrame(-int32_t(f.pushSize()));
}

void
MacroAssembler::Pop(const ValueOperand& val)
{
    popValue(val);
    adjustFrame(-int32_t(sizeof(Value)));
}

void
MacroAssembler::PopStackPtr()
{
    loadPtr(Address(StackPointer, 0), StackPointer);
    adjustFrame(-int32_t(sizeof(intptr_t)));
}


// ===============================================================
// Simple call functions.

CodeOffset
MacroAssembler::call(Register reg)
{
    as_jalr(reg);
    as_nop();
    return CodeOffset(currentOffset());
}

CodeOffset
MacroAssembler::call(Label* label)
{
    ma_bal(label);
    return CodeOffset(currentOffset());
}

CodeOffset
MacroAssembler::callWithPatch()
{
    as_bal(BOffImm16(3 * sizeof(uint32_t)));
    addPtr(Imm32(5 * sizeof(uint32_t)), ra);
    // Allocate space which will be patched by patchCall().
    spew(".space 32bit initValue 0xffff ffff");
    writeInst(UINT32_MAX);
    as_lw(ScratchRegister, ra, -(int32_t)(5 * sizeof(uint32_t)));
    addPtr(ra, ScratchRegister);
    as_jr(ScratchRegister);
    as_nop();
    return CodeOffset(currentOffset());
}

void
MacroAssembler::patchCall(uint32_t callerOffset, uint32_t calleeOffset)
{
    BufferOffset call(callerOffset - 7 * sizeof(uint32_t));

    BOffImm16 offset = BufferOffset(calleeOffset).diffB<BOffImm16>(call);
    if (!offset.isInvalid()) {
        InstImm* bal = (InstImm*)editSrc(call);
        bal->setBOffImm16(offset);
    } else {
        uint32_t u32Offset = callerOffset - 5 * sizeof(uint32_t);
        uint32_t* u32 = reinterpret_cast<uint32_t*>(editSrc(BufferOffset(u32Offset)));
        *u32 = calleeOffset - callerOffset;
    }
}

CodeOffset
MacroAssembler::farJumpWithPatch()
{
    ma_move(SecondScratchReg, ra);
    as_bal(BOffImm16(3 * sizeof(uint32_t)));
    as_lw(ScratchRegister, ra, 0);
    // Allocate space which will be patched by patchFarJump().
    CodeOffset farJump(currentOffset());
    spew(".space 32bit initValue 0xffff ffff");
    writeInst(UINT32_MAX);
    addPtr(ra, ScratchRegister);
    as_jr(ScratchRegister);
    ma_move(ra, SecondScratchReg);
    return farJump;
}

void
MacroAssembler::patchFarJump(CodeOffset farJump, uint32_t targetOffset)
{
    uint32_t* u32 = reinterpret_cast<uint32_t*>(editSrc(BufferOffset(farJump.offset())));
    MOZ_ASSERT(*u32 == UINT32_MAX);
    *u32 = targetOffset - farJump.offset();
}

void
MacroAssembler::call(wasm::SymbolicAddress target)
{
    movePtr(target, CallReg);
    call(CallReg);
}

void
MacroAssembler::call(const Address& addr)
{
    loadPtr(addr, CallReg);
    call(CallReg);
}

void
MacroAssembler::call(ImmWord target)
{
    call(ImmPtr((void*)target.value));
}

void
MacroAssembler::call(ImmPtr target)
{
    BufferOffset bo = m_buffer.nextOffset();
    addPendingJump(bo, target, Relocation::HARDCODED);
    ma_call(target);
}

void
MacroAssembler::call(JitCode* c)
{
    BufferOffset bo = m_buffer.nextOffset();
    addPendingJump(bo, ImmPtr(c->raw()), Relocation::JITCODE);
    ma_liPatchable(ScratchRegister, ImmPtr(c->raw()));
    callJitNoProfiler(ScratchRegister);
}

CodeOffset
MacroAssembler::nopPatchableToCall(const wasm::CallSiteDesc& desc)
{
    CodeOffset offset(currentOffset());
                // MIPS32   //PPC64LE
    as_nop();   // lui      // lui
    as_nop();   // ori      // ori
    as_nop();   // jalr     // drotr32
    as_nop();               // ori
#ifdef JS_CODEGEN_PPC64LE
    as_nop();               //jalr
    as_nop();
#endif
    append(desc, CodeOffset(currentOffset()));
    return offset;
}

void
MacroAssembler::patchNopToCall(uint8_t* call, uint8_t* target)
{
#ifdef JS_CODEGEN_PPC64LE
    Instruction* inst = (Instruction*) call - 6 /* six nops */;
    Assembler::WriteLoad64Instructions(inst, ScratchRegister, (uint64_t) target);
    inst[4] = InstReg(op_special, ScratchRegister, zero, ra, ff_jalr);
#else
    Instruction* inst = (Instruction*) call - 4 /* four nops */;
    Assembler::WriteLuiOriInstructions(inst, &inst[1], ScratchRegister, (uint32_t) target);
    inst[2] = InstReg(op_special, ScratchRegister, zero, ra, ff_jalr);
#endif
}

void
MacroAssembler::patchCallToNop(uint8_t* call)
{
#ifdef JS_CODEGEN_PPC64LE
    Instruction* inst = (Instruction*) call - 6 /* six nops */;
#else
    Instruction* inst = (Instruction*) call - 4 /* four nops */;
#endif

    inst[0].makeNop();
    inst[1].makeNop();
    inst[2].makeNop();
    inst[3].makeNop();
#ifdef JS_CODEGEN_PPC64LE
    inst[4].makeNop();
    inst[5].makeNop();
#endif
}

void
MacroAssembler::pushReturnAddress()
{
    push(ra);
}

void
MacroAssembler::popReturnAddress()
{
    pop(ra);
}

// ===============================================================
// Jit Frames.

uint32_t
MacroAssembler::pushFakeReturnAddress(Register scratch)
{
    CodeLabel cl;

    ma_li(scratch, &cl);
    Push(scratch);
    bind(&cl);
    uint32_t retAddr = currentOffset();

    addCodeLabel(cl);
    return retAddr;
}

void
MacroAssembler::loadStoreBuffer(Register ptr, Register buffer)
{
    if (ptr != buffer)
        movePtr(ptr, buffer);
    orPtr(Imm32(gc::ChunkMask), buffer);
    loadPtr(Address(buffer, gc::ChunkStoreBufferOffsetFromLastByte), buffer);
}

void
MacroAssembler::branchPtrInNurseryChunk(Condition cond, Register ptr, Register temp,
                                        Label* label)
{
    MOZ_ASSERT(cond == Assembler::Equal || cond == Assembler::NotEqual);
    MOZ_ASSERT(ptr != temp);
    MOZ_ASSERT(ptr != SecondScratchReg);

    movePtr(ptr, SecondScratchReg);
    orPtr(Imm32(gc::ChunkMask), SecondScratchReg);
    branch32(cond, Address(SecondScratchReg, gc::ChunkLocationOffsetFromLastByte),
             Imm32(int32_t(gc::ChunkLocation::Nursery)), label);
}

void
MacroAssembler::comment(const char* msg)
{
    Assembler::comment(msg);
}

// ===============================================================
// WebAssembly

CodeOffset
MacroAssembler::wasmTrapInstruction()
{
    CodeOffset offset(currentOffset());
    as_teq(zero, zero, WASM_TRAP);
    return offset;
}

void
MacroAssembler::wasmTruncateDoubleToInt32(FloatRegister input, Register output, bool isSaturating,
                                          Label* oolEntry)
{
    as_truncwd(ScratchFloat32Reg, input);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromFloat32(ScratchFloat32Reg, output);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);
}


void
MacroAssembler::wasmTruncateFloat32ToInt32(FloatRegister input, Register output, bool isSaturating,
                                           Label* oolEntry)
{
    as_truncws(ScratchFloat32Reg, input);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromFloat32(ScratchFloat32Reg, output);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_b(ScratchRegister, Imm32(0), oolEntry, Assembler::NotEqual);
}

void
MacroAssembler::oolWasmTruncateCheckF32ToI32(FloatRegister input, Register output,
                                             TruncFlags flags, wasm::BytecodeOffset off,
                                             Label* rejoin)
{
    outOfLineWasmTruncateToInt32Check(input, output, MIRType::Float32, flags, rejoin, off);
}

void
MacroAssembler::oolWasmTruncateCheckF64ToI32(FloatRegister input, Register output,
                                             TruncFlags flags, wasm::BytecodeOffset off,
                                             Label* rejoin)
{
    outOfLineWasmTruncateToInt32Check(input, output, MIRType::Double, flags, rejoin, off);
}

void
MacroAssembler::oolWasmTruncateCheckF32ToI64(FloatRegister input, Register64 output,
                                             TruncFlags flags, wasm::BytecodeOffset off,
                                             Label* rejoin)
{
    outOfLineWasmTruncateToInt64Check(input, output, MIRType::Float32, flags, rejoin, off);
}

void
MacroAssembler::oolWasmTruncateCheckF64ToI64(FloatRegister input, Register64 output,
                                             TruncFlags flags, wasm::BytecodeOffset off,
                                             Label* rejoin)
{
    outOfLineWasmTruncateToInt64Check(input, output, MIRType::Double, flags, rejoin, off);
}

void
MacroAssemblerMIPSShared::outOfLineWasmTruncateToInt32Check(FloatRegister input, Register output,
                                                            MIRType fromType, TruncFlags flags,
                                                            Label* rejoin,
                                                            wasm::BytecodeOffset trapOffset)
{
    bool isUnsigned = flags & TRUNC_UNSIGNED;
    bool isSaturating = flags & TRUNC_SATURATING;

    if(isSaturating) {

        if(fromType == MIRType::Double)
            asMasm().loadConstantDouble(0.0, ScratchDoubleReg);
        else
            asMasm().loadConstantFloat32(0.0f, ScratchFloat32Reg);

        if(isUnsigned) {

            ma_li(output, Imm32(UINT32_MAX));

            FloatTestKind moveCondition;
            compareFloatingPoint(fromType == MIRType::Double ? DoubleFloat : SingleFloat,
                                 input,
                                 fromType == MIRType::Double ? ScratchDoubleReg : ScratchFloat32Reg,
                                 Assembler::DoubleLessThanOrUnordered, &moveCondition);
            MOZ_ASSERT(moveCondition == TestForTrue);

            as_movt(output, zero);
        } else {

            // Positive overflow is already saturated to INT32_MAX, so we only have
            // to handle NaN and negative overflow here.

            FloatTestKind moveCondition;
            compareFloatingPoint(fromType == MIRType::Double ? DoubleFloat : SingleFloat,
                                 input,
                                 input,
                                 Assembler::DoubleUnordered, &moveCondition);
            MOZ_ASSERT(moveCondition == TestForTrue);

            as_movt(output, zero);

            compareFloatingPoint(fromType == MIRType::Double ? DoubleFloat : SingleFloat,
                                 input,
                                 fromType == MIRType::Double ? ScratchDoubleReg : ScratchFloat32Reg,
                                 Assembler::DoubleLessThan, &moveCondition);
            MOZ_ASSERT(moveCondition == TestForTrue);

            ma_li(ScratchRegister, Imm32(INT32_MIN));
            as_movt(output, ScratchRegister);
        }

        MOZ_ASSERT(rejoin->bound());
        asMasm().jump(rejoin);
        return;
    }

    Label inputIsNaN;

    if (fromType == MIRType::Double)
        asMasm().branchDouble(Assembler::DoubleUnordered, input, input, &inputIsNaN);
    else if (fromType == MIRType::Float32)
        asMasm().branchFloat(Assembler::DoubleUnordered, input, input, &inputIsNaN);

    asMasm().wasmTrap(wasm::Trap::IntegerOverflow, trapOffset);
    asMasm().bind(&inputIsNaN);
    asMasm().wasmTrap(wasm::Trap::InvalidConversionToInteger, trapOffset);
}

void
MacroAssemblerMIPSShared::outOfLineWasmTruncateToInt64Check(FloatRegister input, Register64 output_,
                                                            MIRType fromType, TruncFlags flags,
                                                            Label* rejoin,
                                                            wasm::BytecodeOffset trapOffset)
{
    bool isUnsigned = flags & TRUNC_UNSIGNED;
    bool isSaturating = flags & TRUNC_SATURATING;


    if(isSaturating) {
#if defined(JS_CODEGEN_MIPS32)
        // Saturating callouts don't use ool path.
        return;
#else
        Register output = output_.reg;

        if(fromType == MIRType::Double)
            asMasm().loadConstantDouble(0.0, ScratchDoubleReg);
        else
            asMasm().loadConstantFloat32(0.0f, ScratchFloat32Reg);

        if(isUnsigned) {

            asMasm().ma_li(output, ImmWord(UINT64_MAX));

            FloatTestKind moveCondition;
            compareFloatingPoint(fromType == MIRType::Double ? DoubleFloat : SingleFloat,
                                 input,
                                 fromType == MIRType::Double ? ScratchDoubleReg : ScratchFloat32Reg,
                                 Assembler::DoubleLessThanOrUnordered, &moveCondition);
            MOZ_ASSERT(moveCondition == TestForTrue);

            as_movt(output, zero);
        } else {

            // Positive overflow is already saturated to INT64_MAX, so we only have
            // to handle NaN and negative overflow here.

            FloatTestKind moveCondition;
            compareFloatingPoint(fromType == MIRType::Double ? DoubleFloat : SingleFloat,
                                 input,
                                 input,
                                 Assembler::DoubleUnordered, &moveCondition);
            MOZ_ASSERT(moveCondition == TestForTrue);

            as_movt(output, zero);

            compareFloatingPoint(fromType == MIRType::Double ? DoubleFloat : SingleFloat,
                                 input,
                                 fromType == MIRType::Double ? ScratchDoubleReg : ScratchFloat32Reg,
                                 Assembler::DoubleLessThan, &moveCondition);
            MOZ_ASSERT(moveCondition == TestForTrue);

            asMasm().ma_li(ScratchRegister, ImmWord(INT64_MIN));
            as_movt(output, ScratchRegister);
        }

        MOZ_ASSERT(rejoin->bound());
        asMasm().jump(rejoin);
        return;
#endif

    }

    Label inputIsNaN;

    if (fromType == MIRType::Double)
        asMasm().branchDouble(Assembler::DoubleUnordered, input, input, &inputIsNaN);
    else if (fromType == MIRType::Float32)
        asMasm().branchFloat(Assembler::DoubleUnordered, input, input, &inputIsNaN);

#if defined(JS_CODEGEN_MIPS32)

    // Only possible valid input that produces INT64_MIN result.
    double validInput = isUnsigned ? double(uint64_t(INT64_MIN)) : double(int64_t(INT64_MIN));

    if (fromType == MIRType::Double) {
        asMasm().loadConstantDouble(validInput, ScratchDoubleReg);
        asMasm().branchDouble(Assembler::DoubleEqual, input, ScratchDoubleReg, rejoin);
    } else {
        asMasm().loadConstantFloat32(float(validInput), ScratchFloat32Reg);
        asMasm().branchFloat(Assembler::DoubleEqual, input, ScratchDoubleReg, rejoin);
    }

#endif

    asMasm().wasmTrap(wasm::Trap::IntegerOverflow, trapOffset);
    asMasm().bind(&inputIsNaN);
    asMasm().wasmTrap(wasm::Trap::InvalidConversionToInteger, trapOffset);
}

void
MacroAssembler::wasmLoad(const wasm::MemoryAccessDesc& access, Register memoryBase, Register ptr,
                         Register ptrScratch, AnyRegister output)
{
    wasmLoadImpl(access, memoryBase, ptr, ptrScratch, output, InvalidReg);
}

void
MacroAssembler::wasmUnalignedLoad(const wasm::MemoryAccessDesc& access, Register memoryBase,
                                  Register ptr, Register ptrScratch, Register output, Register tmp)
{
    wasmLoadImpl(access, memoryBase, ptr, ptrScratch, AnyRegister(output), tmp);
}

void
MacroAssembler::wasmUnalignedLoadFP(const wasm::MemoryAccessDesc& access, Register memoryBase,
                                    Register ptr, Register ptrScratch, FloatRegister output,
                                    Register tmp1, Register tmp2, Register tmp3)
{
    MOZ_ASSERT(tmp2 == InvalidReg);
    MOZ_ASSERT(tmp3 == InvalidReg);
    wasmLoadImpl(access, memoryBase, ptr, ptrScratch, AnyRegister(output), tmp1);
}

void
MacroAssembler::wasmStore(const wasm::MemoryAccessDesc& access, AnyRegister value,
                          Register memoryBase, Register ptr, Register ptrScratch)
{
    wasmStoreImpl(access, value, memoryBase, ptr, ptrScratch, InvalidReg);
}

void
MacroAssembler::wasmUnalignedStore(const wasm::MemoryAccessDesc& access, Register value,
                                   Register memoryBase, Register ptr, Register ptrScratch,
                                   Register tmp)
{
    wasmStoreImpl(access, AnyRegister(value), memoryBase, ptr, ptrScratch, tmp);
}

void
MacroAssembler::wasmUnalignedStoreFP(const wasm::MemoryAccessDesc& access, FloatRegister floatValue,
                                     Register memoryBase, Register ptr, Register ptrScratch,
                                     Register tmp)
{
    wasmStoreImpl(access, AnyRegister(floatValue), memoryBase, ptr, ptrScratch, tmp);
}

void
MacroAssemblerMIPSShared::wasmLoadImpl(const wasm::MemoryAccessDesc& access, Register memoryBase,
                                       Register ptr, Register ptrScratch, AnyRegister output,
                                       Register tmp)
{
    uint32_t offset = access.offset();
    MOZ_ASSERT(offset < wasm::OffsetGuardLimit);
    MOZ_ASSERT_IF(offset, ptrScratch != InvalidReg);

    // Maybe add the offset.
    if (offset) {
        asMasm().addPtr(Imm32(offset), ptrScratch);
        ptr = ptrScratch;
    }

    unsigned byteSize = access.byteSize();
    bool isSigned;
    bool isFloat = false;

    switch (access.type()) {
      case Scalar::Int8:    isSigned = true;  break;
      case Scalar::Uint8:   isSigned = false; break;
      case Scalar::Int16:   isSigned = true;  break;
      case Scalar::Uint16:  isSigned = false; break;
      case Scalar::Int32:   isSigned = true;  break;
      case Scalar::Uint32:  isSigned = false; break;
      case Scalar::Float64: isFloat  = true;  break;
      case Scalar::Float32: isFloat  = true;  break;
      default: MOZ_CRASH("unexpected array type");
    }

    BaseIndex address(memoryBase, ptr, TimesOne);
    if (IsUnaligned(access)) {
        MOZ_ASSERT(tmp != InvalidReg);
        if (isFloat) {
            if (byteSize == 4)
                asMasm().loadUnalignedFloat32(access, address, tmp, output.fpu());
            else
                asMasm().loadUnalignedDouble(access, address, tmp, output.fpu());
        } else {
            asMasm().ma_load_unaligned(access, output.gpr(), address, tmp,
                                       static_cast<LoadStoreSize>(8 * byteSize),
                                       isSigned ? SignExtend : ZeroExtend);
        }
        return;
    }

    asMasm().memoryBarrierBefore(access.sync());
    if (isFloat) {
        if (byteSize == 4)
            asMasm().ma_ls(output.fpu(), address);
         else
            asMasm().ma_ld(output.fpu(), address);
    } else {
        asMasm().ma_load(output.gpr(), address, static_cast<LoadStoreSize>(8 * byteSize),
                         isSigned ? SignExtend : ZeroExtend);
    }
    asMasm().append(access, asMasm().size() - 4);
    asMasm().memoryBarrierAfter(access.sync());
}

void
MacroAssemblerMIPSShared::wasmStoreImpl(const wasm::MemoryAccessDesc& access, AnyRegister value,
                                        Register memoryBase, Register ptr, Register ptrScratch,
                                        Register tmp)
{
    uint32_t offset = access.offset();
    MOZ_ASSERT(offset < wasm::OffsetGuardLimit);
    MOZ_ASSERT_IF(offset, ptrScratch != InvalidReg);

    // Maybe add the offset.
    if (offset) {
        asMasm().addPtr(Imm32(offset), ptrScratch);
        ptr = ptrScratch;
    }

    unsigned byteSize = access.byteSize();
    bool isSigned;
    bool isFloat = false;

    switch (access.type()) {
      case Scalar::Int8:    isSigned = true;  break;
      case Scalar::Uint8:   isSigned = false; break;
      case Scalar::Int16:   isSigned = true;  break;
      case Scalar::Uint16:  isSigned = false; break;
      case Scalar::Int32:   isSigned = true;  break;
      case Scalar::Uint32:  isSigned = false; break;
      case Scalar::Int64:   isSigned = true;  break;
      case Scalar::Float64: isFloat  = true;  break;
      case Scalar::Float32: isFloat  = true;  break;
      default: MOZ_CRASH("unexpected array type");
    }

    BaseIndex address(memoryBase, ptr, TimesOne);
    if (IsUnaligned(access)) {
        MOZ_ASSERT(tmp != InvalidReg);
        if (isFloat) {
            if (byteSize == 4)
                asMasm().storeUnalignedFloat32(access, value.fpu(), tmp, address);
            else
                asMasm().storeUnalignedDouble(access, value.fpu(), tmp, address);
        } else {
            asMasm().ma_store_unaligned(access, value.gpr(), address, tmp,
                                        static_cast<LoadStoreSize>(8 * byteSize),
                                        isSigned ? SignExtend : ZeroExtend);
        }
        return;
    }

    asMasm().memoryBarrierBefore(access.sync());
    if (isFloat) {
        if (byteSize == 4)
            asMasm().ma_ss(value.fpu(), address);
        else
            asMasm().ma_sd(value.fpu(), address);
    } else {
        asMasm().ma_store(value.gpr(), address,
                      static_cast<LoadStoreSize>(8 * byteSize),
                      isSigned ? SignExtend : ZeroExtend);
    }
    // Only the last emitted instruction is a memory access.
    asMasm().append(access, asMasm().size() - 4);
    asMasm().memoryBarrierAfter(access.sync());
}

void
MacroAssembler::enterFakeExitFrameForWasm(Register cxreg, Register scratch, ExitFrameType type)
{
    enterFakeExitFrame(cxreg, scratch, type);
}

// ========================================================================
// Primitive atomic operations.

template<typename T>
static void
CompareExchange(MacroAssembler& masm, Scalar::Type type, const Synchronization& sync, const T& mem,
                Register oldval, Register newval, Register valueTemp, Register offsetTemp,
                Register maskTemp, Register output)
{
    bool signExtend = Scalar::isSignedIntType(type);
    unsigned nbytes = Scalar::byteSize(type);

     switch (nbytes) {
        case 1:
        case 2:
            break;
        case 4:
            MOZ_ASSERT(valueTemp == InvalidReg);
            MOZ_ASSERT(offsetTemp == InvalidReg);
            MOZ_ASSERT(maskTemp == InvalidReg);
            break;
        default:
            MOZ_CRASH();
    }

    Label again, end;

    masm.computeEffectiveAddress(mem, SecondScratchReg);

    if (nbytes == 4) {

        masm.memoryBarrierBefore(sync);
        masm.bind(&again);

        masm.as_ll(output, SecondScratchReg, 0);
        masm.ma_b(output, oldval, &end, Assembler::NotEqual, ShortJump);
        masm.ma_move(ScratchRegister, newval);
        masm.as_sc(ScratchRegister, SecondScratchReg, 0);
        masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

        masm.memoryBarrierAfter(sync);
        masm.bind(&end);

        return;
    }

    masm.as_andi(offsetTemp, SecondScratchReg, 3);
    masm.subPtr(offsetTemp, SecondScratchReg);
#if !MOZ_LITTLE_ENDIAN
    masm.as_xori(offsetTemp, offsetTemp, 3);
#endif
    masm.as_sll(offsetTemp, offsetTemp, 3);
    masm.ma_li(maskTemp, Imm32(UINT32_MAX >> ((4 - nbytes) * 8)));
    masm.as_sllv(maskTemp, maskTemp, offsetTemp);
    masm.as_nor(maskTemp, zero, maskTemp);

    masm.memoryBarrierBefore(sync);

    masm.bind(&again);

    masm.as_ll(ScratchRegister, SecondScratchReg, 0);

    masm.as_srlv(output, ScratchRegister, offsetTemp);

    switch (nbytes) {
        case 1:
            if (signExtend) {
                masm.ma_seb(valueTemp, oldval);
                masm.ma_seb(output, output);
            } else {
                masm.as_andi(valueTemp, oldval, 0xff);
                masm.as_andi(output, output, 0xff);
            }
            break;
        case 2:
            if (signExtend) {
                masm.ma_seh(valueTemp, oldval);
                masm.ma_seh(output, output);
            } else {
                masm.as_andi(valueTemp, oldval, 0xffff);
                masm.as_andi(output, output, 0xffff);
            }
            break;
    }

    masm.ma_b(output, valueTemp, &end, Assembler::NotEqual, ShortJump);

    masm.as_sllv(valueTemp, newval, offsetTemp);
    masm.as_and(ScratchRegister, ScratchRegister, maskTemp);
    masm.as_or(ScratchRegister, ScratchRegister, valueTemp);

    masm.as_sc(ScratchRegister, SecondScratchReg, 0);

    masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

    masm.memoryBarrierAfter(sync);

    masm.bind(&end);

}


void
MacroAssembler::compareExchange(Scalar::Type type, const Synchronization& sync, const Address& mem,
                                Register oldval, Register newval, Register valueTemp,
                                Register offsetTemp, Register maskTemp, Register output)
{
    CompareExchange(*this, type, sync, mem, oldval, newval, valueTemp, offsetTemp, maskTemp,
                    output);
}

void
MacroAssembler::compareExchange(Scalar::Type type, const Synchronization& sync, const BaseIndex& mem,
                                Register oldval, Register newval, Register valueTemp,
                                Register offsetTemp, Register maskTemp, Register output)
{
    CompareExchange(*this, type, sync, mem, oldval, newval, valueTemp, offsetTemp, maskTemp,
                    output);
}


template<typename T>
static void
AtomicExchange(MacroAssembler& masm, Scalar::Type type, const Synchronization& sync, const T& mem,
               Register value, Register valueTemp, Register offsetTemp, Register maskTemp,
               Register output)
{
    bool signExtend = Scalar::isSignedIntType(type);
    unsigned nbytes = Scalar::byteSize(type);

     switch (nbytes) {
        case 1:
        case 2:
            break;
        case 4:
            MOZ_ASSERT(valueTemp == InvalidReg);
            MOZ_ASSERT(offsetTemp == InvalidReg);
            MOZ_ASSERT(maskTemp == InvalidReg);
            break;
        default:
            MOZ_CRASH();
    }

    Label again;

    masm.computeEffectiveAddress(mem, SecondScratchReg);

    if (nbytes == 4) {

        masm.memoryBarrierBefore(sync);
        masm.bind(&again);

        masm.as_ll(output, SecondScratchReg, 0);
        masm.ma_move(ScratchRegister, value);
        masm.as_sc(ScratchRegister, SecondScratchReg, 0);
        masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

        masm.memoryBarrierAfter(sync);

        return;
    }

    masm.as_andi(offsetTemp, SecondScratchReg, 3);
    masm.subPtr(offsetTemp, SecondScratchReg);
#if !MOZ_LITTLE_ENDIAN
    masm.as_xori(offsetTemp, offsetTemp, 3);
#endif
    masm.as_sll(offsetTemp, offsetTemp, 3);
    masm.ma_li(maskTemp, Imm32(UINT32_MAX >> ((4 - nbytes) * 8)));
    masm.as_sllv(maskTemp, maskTemp, offsetTemp);
    masm.as_nor(maskTemp, zero, maskTemp);
    switch (nbytes) {
        case 1:
            masm.as_andi(valueTemp, value, 0xff);
            break;
        case 2:
            masm.as_andi(valueTemp, value, 0xffff);
            break;
    }
    masm.as_sllv(valueTemp, valueTemp, offsetTemp);

    masm.memoryBarrierBefore(sync);

    masm.bind(&again);

    masm.as_ll(output, SecondScratchReg, 0);
    masm.as_and(ScratchRegister, output, maskTemp);
    masm.as_or(ScratchRegister, ScratchRegister, valueTemp);

    masm.as_sc(ScratchRegister, SecondScratchReg, 0);

    masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

    masm.as_srlv(output, output, offsetTemp);

    switch (nbytes) {
        case 1:
            if (signExtend) {
                masm.ma_seb(output, output);
            } else {
                masm.as_andi(output, output, 0xff);
            }
            break;
        case 2:
            if (signExtend) {
                masm.ma_seh(output, output);
            } else {
                masm.as_andi(output, output, 0xffff);
            }
            break;
    }

    masm.memoryBarrierAfter(sync);
}


void
MacroAssembler::atomicExchange(Scalar::Type type, const Synchronization& sync, const Address& mem,
                               Register value, Register valueTemp, Register offsetTemp,
                               Register maskTemp, Register output)
{
    AtomicExchange(*this, type, sync, mem, value, valueTemp, offsetTemp, maskTemp, output);
}

void
MacroAssembler::atomicExchange(Scalar::Type type, const Synchronization& sync, const BaseIndex& mem,
                               Register value, Register valueTemp, Register offsetTemp,
                               Register maskTemp, Register output)
{
    AtomicExchange(*this, type, sync, mem, value, valueTemp, offsetTemp, maskTemp, output);
}


template<typename T>
static void
AtomicFetchOp(MacroAssembler& masm, Scalar::Type type, const Synchronization& sync,
              AtomicOp op, const T& mem, Register value, Register valueTemp,
              Register offsetTemp, Register maskTemp, Register output)
{
    bool signExtend = Scalar::isSignedIntType(type);
    unsigned nbytes = Scalar::byteSize(type);

     switch (nbytes) {
        case 1:
        case 2:
            break;
        case 4:
            MOZ_ASSERT(valueTemp == InvalidReg);
            MOZ_ASSERT(offsetTemp == InvalidReg);
            MOZ_ASSERT(maskTemp == InvalidReg);
            break;
        default:
            MOZ_CRASH();
    }

    Label again;

    masm.computeEffectiveAddress(mem, SecondScratchReg);

    if (nbytes == 4) {

        masm.memoryBarrierBefore(sync);
        masm.bind(&again);

        masm.as_ll(output, SecondScratchReg, 0);

        switch (op) {
        case AtomicFetchAddOp:
            masm.as_addu(ScratchRegister, output, value);
            break;
        case AtomicFetchSubOp:
            masm.as_subu(ScratchRegister, output, value);
            break;
        case AtomicFetchAndOp:
            masm.as_and(ScratchRegister, output, value);
            break;
        case AtomicFetchOrOp:
            masm.as_or(ScratchRegister, output, value);
            break;
        case AtomicFetchXorOp:
            masm.as_xor(ScratchRegister, output, value);
            break;
        default:
            MOZ_CRASH();
        }

        masm.as_sc(ScratchRegister, SecondScratchReg, 0);
        masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

        masm.memoryBarrierAfter(sync);

        return;
    }


    masm.as_andi(offsetTemp, SecondScratchReg, 3);
    masm.subPtr(offsetTemp, SecondScratchReg);
#if !MOZ_LITTLE_ENDIAN
    masm.as_xori(offsetTemp, offsetTemp, 3);
#endif
    masm.as_sll(offsetTemp, offsetTemp, 3);
    masm.ma_li(maskTemp, Imm32(UINT32_MAX >> ((4 - nbytes) * 8)));
    masm.as_sllv(maskTemp, maskTemp, offsetTemp);
    masm.as_nor(maskTemp, zero, maskTemp);

    masm.memoryBarrierBefore(sync);

    masm.bind(&again);

    masm.as_ll(ScratchRegister, SecondScratchReg, 0);
    masm.as_srlv(output, ScratchRegister, offsetTemp);

    switch (op) {
        case AtomicFetchAddOp:
            masm.as_addu(valueTemp, output, value);
            break;
        case AtomicFetchSubOp:
            masm.as_subu(valueTemp, output, value);
            break;
        case AtomicFetchAndOp:
            masm.as_and(valueTemp, output, value);
            break;
        case AtomicFetchOrOp:
            masm.as_or(valueTemp, output, value);
            break;
        case AtomicFetchXorOp:
            masm.as_xor(valueTemp, output, value);
            break;
        default:
            MOZ_CRASH();
    }

    switch (nbytes) {
        case 1:
            masm.as_andi(valueTemp, valueTemp, 0xff);
            break;
        case 2:
            masm.as_andi(valueTemp, valueTemp, 0xffff);
            break;
    }

    masm.as_sllv(valueTemp, valueTemp, offsetTemp);

    masm.as_and(ScratchRegister, ScratchRegister, maskTemp);
    masm.as_or(ScratchRegister, ScratchRegister, valueTemp);

    masm.as_sc(ScratchRegister, SecondScratchReg, 0);

    masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

    switch (nbytes) {
        case 1:
            if (signExtend) {
                masm.ma_seb(output, output);
            } else {
                masm.as_andi(output, output, 0xff);
            }
            break;
        case 2:
            if (signExtend) {
                masm.ma_seh(output, output);
            } else {
                masm.as_andi(output, output, 0xffff);
            }
            break;
    }

    masm.memoryBarrierAfter(sync);
}

void
MacroAssembler::atomicFetchOp(Scalar::Type type, const Synchronization& sync, AtomicOp op,
                              Register value, const Address& mem, Register valueTemp,
                              Register offsetTemp, Register maskTemp, Register output)
{
    AtomicFetchOp(*this, type, sync, op, mem, value, valueTemp, offsetTemp, maskTemp, output);
}

void
MacroAssembler::atomicFetchOp(Scalar::Type type, const Synchronization& sync, AtomicOp op,
                              Register value, const BaseIndex& mem, Register valueTemp,
                              Register offsetTemp, Register maskTemp, Register output)
{
    AtomicFetchOp(*this, type, sync, op, mem, value, valueTemp, offsetTemp, maskTemp, output);
}

template<typename T>
static void
AtomicEffectOp(MacroAssembler& masm, Scalar::Type type, const Synchronization& sync, AtomicOp op,
        const T& mem, Register value, Register valueTemp, Register offsetTemp, Register maskTemp)
{
    unsigned nbytes = Scalar::byteSize(type);

     switch (nbytes) {
        case 1:
        case 2:
            break;
        case 4:
            MOZ_ASSERT(valueTemp == InvalidReg);
            MOZ_ASSERT(offsetTemp == InvalidReg);
            MOZ_ASSERT(maskTemp == InvalidReg);
            break;
        default:
            MOZ_CRASH();
    }

    Label again;

    masm.computeEffectiveAddress(mem, SecondScratchReg);

    if (nbytes == 4) {

        masm.memoryBarrierBefore(sync);
        masm.bind(&again);

        masm.as_ll(ScratchRegister, SecondScratchReg, 0);

        switch (op) {
        case AtomicFetchAddOp:
            masm.as_addu(ScratchRegister, ScratchRegister, value);
            break;
        case AtomicFetchSubOp:
            masm.as_subu(ScratchRegister, ScratchRegister, value);
            break;
        case AtomicFetchAndOp:
            masm.as_and(ScratchRegister, ScratchRegister, value);
            break;
        case AtomicFetchOrOp:
            masm.as_or(ScratchRegister, ScratchRegister, value);
            break;
        case AtomicFetchXorOp:
            masm.as_xor(ScratchRegister, ScratchRegister, value);
            break;
        default:
            MOZ_CRASH();
        }

        masm.as_sc(ScratchRegister, SecondScratchReg, 0);
        masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

        masm.memoryBarrierAfter(sync);

        return;
    }

    masm.as_andi(offsetTemp, SecondScratchReg, 3);
    masm.subPtr(offsetTemp, SecondScratchReg);
#if !MOZ_LITTLE_ENDIAN
    masm.as_xori(offsetTemp, offsetTemp, 3);
#endif
    masm.as_sll(offsetTemp, offsetTemp, 3);
    masm.ma_li(maskTemp, Imm32(UINT32_MAX >> ((4 - nbytes) * 8)));
    masm.as_sllv(maskTemp, maskTemp, offsetTemp);
    masm.as_nor(maskTemp, zero, maskTemp);

    masm.memoryBarrierBefore(sync);

    masm.bind(&again);

    masm.as_ll(ScratchRegister, SecondScratchReg, 0);
    masm.as_srlv(valueTemp, ScratchRegister, offsetTemp);

    switch (op) {
        case AtomicFetchAddOp:
            masm.as_addu(valueTemp, valueTemp, value);
            break;
        case AtomicFetchSubOp:
            masm.as_subu(valueTemp, valueTemp, value);
            break;
        case AtomicFetchAndOp:
            masm.as_and(valueTemp, valueTemp, value);
            break;
        case AtomicFetchOrOp:
            masm.as_or(valueTemp, valueTemp, value);
            break;
        case AtomicFetchXorOp:
            masm.as_xor(valueTemp, valueTemp, value);
            break;
        default:
            MOZ_CRASH();
    }

    switch (nbytes) {
        case 1:
            masm.as_andi(valueTemp, valueTemp, 0xff);
            break;
        case 2:
            masm.as_andi(valueTemp, valueTemp, 0xffff);
            break;
    }

    masm.as_sllv(valueTemp, valueTemp, offsetTemp);

    masm.as_and(ScratchRegister, ScratchRegister, maskTemp);
    masm.as_or(ScratchRegister, ScratchRegister, valueTemp);

    masm.as_sc(ScratchRegister, SecondScratchReg, 0);

    masm.ma_b(ScratchRegister, ScratchRegister, &again, Assembler::Zero, ShortJump);

    masm.memoryBarrierAfter(sync);
}


void
MacroAssembler::atomicEffectOp(Scalar::Type type, const Synchronization& sync, AtomicOp op,
                               Register value, const Address& mem, Register valueTemp,
                               Register offsetTemp, Register maskTemp)
{
    AtomicEffectOp(*this, type, sync, op, mem, value, valueTemp, offsetTemp, maskTemp);
}

void
MacroAssembler::atomicEffectOp(Scalar::Type type, const Synchronization& sync, AtomicOp op,
                               Register value, const BaseIndex& mem, Register valueTemp,
                               Register offsetTemp, Register maskTemp)
{
    AtomicEffectOp(*this, type, sync, op, mem, value, valueTemp, offsetTemp, maskTemp);
}

// ========================================================================
// JS atomic operations.

template<typename T>
static void
CompareExchangeJS(MacroAssembler& masm, Scalar::Type arrayType, const Synchronization& sync,
                  const T& mem, Register oldval, Register newval, Register valueTemp,
                  Register offsetTemp, Register maskTemp, Register temp, AnyRegister output)
{
    if (arrayType == Scalar::Uint32) {
        masm.compareExchange(arrayType, sync, mem, oldval, newval, valueTemp, offsetTemp, maskTemp,
                             temp);
        masm.convertUInt32ToDouble(temp, output.fpu());
    } else {
        masm.compareExchange(arrayType, sync, mem, oldval, newval, valueTemp, offsetTemp, maskTemp,
                             output.gpr());
    }
}

void
MacroAssembler::compareExchangeJS(Scalar::Type arrayType, const Synchronization& sync,
                                  const Address& mem, Register oldval, Register newval,
                                  Register valueTemp, Register offsetTemp, Register maskTemp,
                                  Register temp, AnyRegister output)
{
    CompareExchangeJS(*this, arrayType, sync, mem, oldval, newval, valueTemp, offsetTemp, maskTemp,
                      temp, output);
}

void
MacroAssembler::compareExchangeJS(Scalar::Type arrayType, const Synchronization& sync,
                                  const BaseIndex& mem, Register oldval, Register newval,
                                  Register valueTemp, Register offsetTemp, Register maskTemp,
                                  Register temp, AnyRegister output)
{
    CompareExchangeJS(*this, arrayType, sync, mem, oldval, newval,valueTemp, offsetTemp, maskTemp,
                      temp, output);
}

template<typename T>
static void
AtomicExchangeJS(MacroAssembler& masm, Scalar::Type arrayType, const Synchronization& sync,
                 const T& mem, Register value, Register valueTemp,
                 Register offsetTemp, Register maskTemp, Register temp, AnyRegister output)
{
    if (arrayType == Scalar::Uint32) {
        masm.atomicExchange(arrayType, sync, mem, value, valueTemp, offsetTemp, maskTemp, temp);
        masm.convertUInt32ToDouble(temp, output.fpu());
    } else {
        masm.atomicExchange(arrayType, sync, mem, value, valueTemp, offsetTemp, maskTemp,
                            output.gpr());
    }
}

void
MacroAssembler::atomicExchangeJS(Scalar::Type arrayType, const Synchronization& sync,
                                 const Address& mem, Register value, Register valueTemp,
                                 Register offsetTemp, Register maskTemp, Register temp,
                                 AnyRegister output)
{
    AtomicExchangeJS(*this, arrayType, sync, mem, value, valueTemp, offsetTemp, maskTemp, temp,
                     output);
}

void
MacroAssembler::atomicExchangeJS(Scalar::Type arrayType, const Synchronization& sync,
                                 const BaseIndex& mem, Register value, Register valueTemp,
                                 Register offsetTemp, Register maskTemp, Register temp,
                                 AnyRegister output)
{
    AtomicExchangeJS(*this, arrayType, sync, mem, value, valueTemp, offsetTemp, maskTemp, temp, output);
}

template<typename T>
static void
AtomicFetchOpJS(MacroAssembler& masm, Scalar::Type arrayType, const Synchronization& sync,
                AtomicOp op, Register value, const T& mem, Register valueTemp,
                Register offsetTemp, Register maskTemp, Register temp,
                AnyRegister output)
{
    if (arrayType == Scalar::Uint32) {
        masm.atomicFetchOp(arrayType, sync, op, value, mem, valueTemp, offsetTemp, maskTemp, temp);
        masm.convertUInt32ToDouble(temp, output.fpu());
    } else {
        masm.atomicFetchOp(arrayType, sync, op, value, mem, valueTemp, offsetTemp, maskTemp,
                           output.gpr());
    }
}

void
MacroAssembler::atomicFetchOpJS(Scalar::Type arrayType, const Synchronization& sync, AtomicOp op,
                                Register value, const Address& mem, Register valueTemp,
                                Register offsetTemp, Register maskTemp, Register temp,
                                AnyRegister output)
{
    AtomicFetchOpJS(*this, arrayType, sync, op, value, mem, valueTemp, offsetTemp, maskTemp, temp,
                    output);
}

void
MacroAssembler::atomicFetchOpJS(Scalar::Type arrayType, const Synchronization& sync, AtomicOp op,
                                Register value, const BaseIndex& mem, Register valueTemp,
                                Register offsetTemp, Register maskTemp, Register temp,
                                AnyRegister output)
{
    AtomicFetchOpJS(*this, arrayType, sync, op, value, mem, valueTemp, offsetTemp, maskTemp, temp,
                    output);
}

void
MacroAssembler::atomicEffectOpJS(Scalar::Type arrayType, const Synchronization& sync, AtomicOp op,
                                 Register value, const BaseIndex& mem, Register valueTemp,
                                 Register offsetTemp, Register maskTemp)
{
    atomicEffectOp(arrayType, sync, op, value, mem, valueTemp, offsetTemp, maskTemp);
}

void
MacroAssembler::atomicEffectOpJS(Scalar::Type arrayType, const Synchronization& sync, AtomicOp op,
                                 Register value, const Address& mem, Register valueTemp,
                                 Register offsetTemp, Register maskTemp)
{
    atomicEffectOp(arrayType, sync, op, value, mem, valueTemp, offsetTemp, maskTemp);
}

// ========================================================================
// Spectre Mitigations.

void
MacroAssembler::speculationBarrier()
{
    MOZ_CRASH();
}
