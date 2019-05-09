/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef jit_ppc64le_MacroAssembler_ppc64le_inl_h
#define jit_ppc64le_MacroAssembler_ppc64le_inl_h

#include "jit/ppc64le/MacroAssembler-ppc64le.h"

namespace js {
namespace jit {

//{{{ check_macroassembler_style

void
MacroAssembler::move64(Register64 src, Register64 dest)
{
    movePtr(src.reg, dest.reg);
}

void
MacroAssembler::move64(Imm64 imm, Register64 dest)
{
    movePtr(ImmWord(imm.value), dest.reg);
}

void
MacroAssembler::moveDoubleToGPR64(FloatRegister src, Register64 dest)
{
    moveFromDouble(src, dest.reg);
}

void
MacroAssembler::moveGPR64ToDouble(Register64 src, FloatRegister dest)
{
    moveToDouble(src.reg, dest);
}

void
MacroAssembler::move64To32(Register64 src, Register dest)
{
    // Registers are registers, so why should it be:
    // 32 bits are treated differently?
    // (with apologies to Depeche Mode)
    // Seriously, XXX: should we mask the upper word off??
    as_or(dest, src.reg, src.reg);
}

void
MacroAssembler::move32To64ZeroExtend(Register src, Register64 dest)
{
    // If the register was loaded with lwz or otherwise
    // the upper word was cleared, a simple move suffices.
    as_or(dest.reg, src, src);
}

void
MacroAssembler::move8To64SignExtend(Register src, Register64 dest)
{
    move32To64SignExtend(src, dest);
    move8SignExtend(dest.reg, dest.reg);
}

void
MacroAssembler::move16To64SignExtend(Register src, Register64 dest)
{
    move32To64SignExtend(src, dest);
    move16SignExtend(dest.reg, dest.reg);
}

void
MacroAssembler::move32To64SignExtend(Register src, Register64 dest)
{
    as_extsw(dest.reg, src);
}

// ===============================================================
// Logical instructions

void
MacroAssembler::andPtr(Register src, Register dest)
{
    ma_and(dest, src);
}

void
MacroAssembler::andPtr(Imm32 imm, Register dest)
{
    ma_and(dest, imm);
}

void
MacroAssembler::and64(Imm64 imm, Register64 dest)
{
    ma_li(ScratchRegister, ImmWord(imm.value));
    ma_and(dest.reg, ScratchRegister);
}

void
MacroAssembler::and64(Register64 src, Register64 dest)
{
    ma_and(dest.reg, src.reg);
}

void
MacroAssembler::and64(const Operand& src, Register64 dest)
{
    if (src.getTag() == Operand::MEM) {
        Register64 scratch(ScratchRegister);

        load64(src.toAddress(), scratch);
        and64(scratch, dest);
    } else {
        and64(Register64(src.toReg()), dest);
    }
}

void
MacroAssembler::or64(Imm64 imm, Register64 dest)
{
    ma_li(ScratchRegister, ImmWord(imm.value));
    ma_or(dest.reg, ScratchRegister);
}

void
MacroAssembler::xor64(Imm64 imm, Register64 dest)
{
    ma_li(ScratchRegister, ImmWord(imm.value));
    ma_xor(dest.reg, ScratchRegister);
}

void
MacroAssembler::orPtr(Register src, Register dest)
{
    ma_or(dest, src);
}

void
MacroAssembler::orPtr(Imm32 imm, Register dest)
{
    ma_or(dest, imm);
}

void
MacroAssembler::or64(Register64 src, Register64 dest)
{
    ma_or(dest.reg, src.reg);
}

void
MacroAssembler::or64(const Operand& src, Register64 dest)
{
    if (src.getTag() == Operand::MEM) {
        Register64 scratch(ScratchRegister);

        load64(src.toAddress(), scratch);
        or64(scratch, dest);
    } else {
        or64(Register64(src.toReg()), dest);
    }
}

void
MacroAssembler::xor64(Register64 src, Register64 dest)
{
    ma_xor(dest.reg, src.reg);
}

void
MacroAssembler::xor64(const Operand& src, Register64 dest)
{
    if (src.getTag() == Operand::MEM) {
        Register64 scratch(ScratchRegister);

        load64(src.toAddress(), scratch);
        xor64(scratch, dest);
    } else {
        xor64(Register64(src.toReg()), dest);
    }
}

void
MacroAssembler::xorPtr(Register src, Register dest)
{
    ma_xor(dest, src);
}

void
MacroAssembler::xorPtr(Imm32 imm, Register dest)
{
    ma_xor(dest, imm);
}

// ===============================================================
// Arithmetic functions

void
MacroAssembler::addPtr(Register src, Register dest)
{
    ma_daddu(dest, src);
}

void
MacroAssembler::addPtr(Imm32 imm, Register dest)
{
    ma_daddu(dest, imm);
}

void
MacroAssembler::addPtr(ImmWord imm, Register dest)
{
    movePtr(imm, ScratchRegister);
    addPtr(ScratchRegister, dest);
}

void
MacroAssembler::add64(Register64 src, Register64 dest)
{
    addPtr(src.reg, dest.reg);
}

void
MacroAssembler::add64(const Operand& src, Register64 dest)
{
    if (src.getTag() == Operand::MEM) {
        Register64 scratch(ScratchRegister);

        load64(src.toAddress(), scratch);
        add64(scratch, dest);
    } else {
        add64(Register64(src.toReg()), dest);
    }
}

void
MacroAssembler::add64(Imm32 imm, Register64 dest)
{
    ma_daddu(dest.reg, imm);
}

void
MacroAssembler::add64(Imm64 imm, Register64 dest)
{
    MOZ_ASSERT(dest.reg != ScratchRegister);
    mov(ImmWord(imm.value), ScratchRegister);
    ma_daddu(dest.reg, ScratchRegister);
}

CodeOffset
MacroAssembler::sub32FromStackPtrWithPatch(Register dest)
{
    CodeOffset offset = CodeOffset(currentOffset());
    MacroAssemblerPPC64LE::ma_liPatchable(dest, Imm32(0));
    as_subf(dest, dest, StackPointer); // T = B - A
    return offset;
}

void
MacroAssembler::patchSub32FromStackPtr(CodeOffset offset, Imm32 imm)
{
    Instruction* lis = (Instruction*) m_buffer.getInst(BufferOffset(offset.offset()));
    MOZ_ASSERT(lis->extractOpcode() == ((uint32_t)op_lis >> OpcodeShift));
    MOZ_ASSERT(lis->next()->extractOpcode() == ((uint32_t)op_ori >> OpcodeShift));

    MacroAssemblerPPC64LE::UpdateLisOriValue(lis, lis->next(), imm.value);
}

void
MacroAssembler::subPtr(Register src, Register dest)
{
    as_subf(dest, src, dest); // T = B - A
}

void
MacroAssembler::subPtr(Imm32 imm, Register dest)
{
    ma_dsubu(dest, dest, imm); // inverted at MacroAssembler level
}

void
MacroAssembler::sub64(Register64 src, Register64 dest)
{
    as_subf(dest.reg, src.reg, dest.reg);
}

void
MacroAssembler::sub64(const Operand& src, Register64 dest)
{
    if (src.getTag() == Operand::MEM) {
        Register64 scratch(ScratchRegister);

        load64(src.toAddress(), scratch);
        sub64(scratch, dest);
    } else {
        sub64(Register64(src.toReg()), dest);
    }
}

void
MacroAssembler::sub64(Imm64 imm, Register64 dest)
{
    MOZ_ASSERT(dest.reg != ScratchRegister);
    mov(ImmWord(imm.value), ScratchRegister);
    as_subf(dest.reg, ScratchRegister, dest.reg); // T = B - A
}

void
MacroAssembler::mul64(Imm64 imm, const Register64& dest)
{
    MOZ_ASSERT(dest.reg != ScratchRegister);
    mov(ImmWord(imm.value), ScratchRegister);
    as_mulld(dest.reg, ScratchRegister, dest.reg); // low order word
}

void
MacroAssembler::mul64(Imm64 imm, const Register64& dest, const Register temp)
{
    MOZ_ASSERT(temp == InvalidReg);
    mul64(imm, dest);
}

void
MacroAssembler::mul64(const Register64& src, const Register64& dest, const Register temp)
{
    MOZ_ASSERT(temp == InvalidReg);
    as_mulld(dest.reg, src.reg, dest.reg); // low order word
}

void
MacroAssembler::mul64(const Operand& src, const Register64& dest, const Register temp)
{
    if (src.getTag() == Operand::MEM) {
        Register64 scratch(ScratchRegister);

        load64(src.toAddress(), scratch);
        mul64(scratch, dest, temp);
    } else {
        mul64(Register64(src.toReg()), dest, temp);
    }
}

void
MacroAssembler::mulBy3(Register src, Register dest)
{
    // I guess this *is* better than mulli.
    MOZ_ASSERT(src != ScratchRegister);
    as_add(ScratchRegister, src, src);
    as_add(dest, ScratchRegister, src);
}

void
MacroAssembler::inc64(AbsoluteAddress dest)
{
    ma_li(ScratchRegister, ImmWord(uintptr_t(dest.addr)));
    as_ld(SecondScratchReg, ScratchRegister, 0);
    as_addi(SecondScratchReg, SecondScratchReg, 1);
    as_std(SecondScratchReg, ScratchRegister, 0);
}

void
MacroAssembler::neg64(Register64 reg)
{
    as_neg(reg.reg, reg.reg);
}

// ===============================================================
// Shift functions

void
MacroAssembler::lshiftPtr(Imm32 imm, Register dest)
{
    MOZ_ASSERT(0 <= imm.value && imm.value < 64);
    ma_dsll(dest, dest, imm);
}

void
MacroAssembler::lshift64(Imm32 imm, Register64 dest)
{
    MOZ_ASSERT(0 <= imm.value && imm.value < 64);
    ma_dsll(dest.reg, dest.reg, imm);
}

void
MacroAssembler::lshift64(Register shift, Register64 dest)
{
    ma_dsll(dest.reg, dest.reg, shift);
}

void
MacroAssembler::rshiftPtr(Imm32 imm, Register dest)
{
    MOZ_ASSERT(0 <= imm.value && imm.value < 64);
    ma_dsrl(dest, dest, imm);
}

void
MacroAssembler::rshift64(Imm32 imm, Register64 dest)
{
    MOZ_ASSERT(0 <= imm.value && imm.value < 64);
    ma_dsrl(dest.reg, dest.reg, imm);
}

void
MacroAssembler::rshift64(Register shift, Register64 dest)
{
    ma_dsrl(dest.reg, dest.reg, shift);
}

void
MacroAssembler::rshiftPtrArithmetic(Imm32 imm, Register dest)
{
    MOZ_ASSERT(0 <= imm.value && imm.value < 64);
    ma_dsra(dest, dest, imm);
}

void
MacroAssembler::rshift64Arithmetic(Imm32 imm, Register64 dest)
{
    MOZ_ASSERT(0 <= imm.value && imm.value < 64);
    ma_dsra(dest.reg, dest.reg, imm);
}

void
MacroAssembler::rshift64Arithmetic(Register shift, Register64 dest)
{
    ma_dsra(dest.reg, dest.reg, shift);
}

// ===============================================================
// Rotation functions

void
MacroAssembler::rotateLeft64(Imm32 count, Register64 src, Register64 dest, Register temp)
{
    MOZ_ASSERT(temp == InvalidReg);

    if (count.value)
        ma_drol(dest.reg, src.reg, count);
    else
        ma_move(dest.reg, src.reg);
}

void
MacroAssembler::rotateLeft64(Register count, Register64 src, Register64 dest, Register temp)
{
    MOZ_ASSERT(temp == InvalidReg);
    ma_drol(dest.reg, src.reg, count);
}

void
MacroAssembler::rotateRight64(Imm32 count, Register64 src, Register64 dest, Register temp)
{
    MOZ_ASSERT(temp == InvalidReg);

    if (count.value)
        ma_dror(dest.reg, src.reg, count);
    else
        ma_move(dest.reg, src.reg);
}

void
MacroAssembler::rotateRight64(Register count, Register64 src, Register64 dest, Register temp)
{
    MOZ_ASSERT(temp == InvalidReg);
    ma_dror(dest.reg, src.reg, count);
}

// ===============================================================
// Condition functions

template <typename T1, typename T2>
void
MacroAssembler::cmpPtrSet(Condition cond, T1 lhs, T2 rhs, Register dest)
{
    ma_cmp_set(dest, lhs, rhs, cond);
}

// Also see below for specializations of cmpPtrSet.

template <typename T1, typename T2>
void
MacroAssembler::cmp32Set(Condition cond, T1 lhs, T2 rhs, Register dest)
{
    ma_cmp_set(dest, lhs, rhs, cond);
}

// ===============================================================
// Bit counting functions

void
MacroAssembler::clz64(Register64 src, Register dest)
{
    as_dclz(dest, src.reg);
}

void
MacroAssembler::ctz64(Register64 src, Register dest)
{
    ma_dctz(dest, src.reg);
}

void
MacroAssembler::popcnt64(Register64 input, Register64 output, Register tmp)
{
    ma_move(output.reg, input.reg);
    ma_dsra(tmp, input.reg, Imm32(1));
    ma_li(ScratchRegister, ImmWord(0x5555555555555555UL));
    ma_and(tmp, ScratchRegister);
    ma_dsubu(output.reg, tmp);
    ma_dsra(tmp, output.reg, Imm32(2));
    ma_li(ScratchRegister, ImmWord(0x3333333333333333UL));
    ma_and(output.reg, ScratchRegister);
    ma_and(tmp, ScratchRegister);
    ma_daddu(output.reg, tmp);
    ma_dsrl(tmp, output.reg, Imm32(4));
    ma_daddu(output.reg, tmp);
    ma_li(ScratchRegister, ImmWord(0xF0F0F0F0F0F0F0FUL));
    ma_and(output.reg, ScratchRegister);
    ma_dsll(tmp, output.reg, Imm32(8));
    ma_daddu(output.reg, tmp);
    ma_dsll(tmp, output.reg, Imm32(16));
    ma_daddu(output.reg, tmp);
    ma_dsll(tmp, output.reg, Imm32(32));
    ma_daddu(output.reg, tmp);
    ma_dsra(output.reg, output.reg, Imm32(56));
}

// ===============================================================
// Branch functions

void
MacroAssembler::branch64(Condition cond, Register64 lhs, Imm64 val, Label* success, Label* fail)
{
    MOZ_ASSERT(cond == Assembler::NotEqual || cond == Assembler::Equal ||
               cond == Assembler::LessThan || cond == Assembler::LessThanOrEqual ||
               cond == Assembler::GreaterThan || cond == Assembler::GreaterThanOrEqual ||
               cond == Assembler::Below || cond == Assembler::BelowOrEqual ||
               cond == Assembler::Above || cond == Assembler::AboveOrEqual,
               "other condition codes not supported");

    branchPtr(cond, lhs.reg, ImmWord(val.value), success);
    if (fail)
        jump(fail);
}

void
MacroAssembler::branch64(Condition cond, Register64 lhs, Register64 rhs, Label* success, Label* fail)
{
    MOZ_ASSERT(cond == Assembler::NotEqual || cond == Assembler::Equal ||
               cond == Assembler::LessThan || cond == Assembler::LessThanOrEqual ||
               cond == Assembler::GreaterThan || cond == Assembler::GreaterThanOrEqual ||
               cond == Assembler::Below || cond == Assembler::BelowOrEqual ||
               cond == Assembler::Above || cond == Assembler::AboveOrEqual,
               "other condition codes not supported");

    branchPtr(cond, lhs.reg, rhs.reg, success);
    if (fail)
        jump(fail);
}

void
MacroAssembler::branch64(Condition cond, const Address& lhs, Imm64 val, Label* label)
{
    MOZ_ASSERT(cond == Assembler::NotEqual,
               "other condition codes not supported");

    branchPtr(cond, lhs, ImmWord(val.value), label);
}

void
MacroAssembler::branch64(Condition cond, const Address& lhs, const Address& rhs, Register scratch,
                         Label* label)
{
    MOZ_ASSERT(cond == Assembler::NotEqual,
               "other condition codes not supported");
    MOZ_ASSERT(lhs.base != scratch);
    MOZ_ASSERT(rhs.base != scratch);

    loadPtr(rhs, scratch);
    branchPtr(cond, lhs, scratch, label);
}

void
MacroAssembler::branchPrivatePtr(Condition cond, const Address& lhs, Register rhs, Label* label)
{
    if (rhs != ScratchRegister)
        movePtr(rhs, ScratchRegister);
    // Instead of unboxing lhs, box rhs and do direct comparison with lhs.
    rshiftPtr(Imm32(1), ScratchRegister);
    branchPtr(cond, lhs, ScratchRegister, label);
}

template <class L>
void
MacroAssembler::branchTest64(Condition cond, Register64 lhs, Register64 rhs, Register temp,
                             L label)
{
    branchTestPtr(cond, lhs.reg, rhs.reg, label);
}

void
MacroAssembler::branchTestUndefined(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestUndefined(cond, scratch2, label);
}

void
MacroAssembler::branchTestInt32(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestInt32(cond, scratch2, label);
}

void
MacroAssembler::branchTestInt32Truthy(bool b, const ValueOperand& value, Label* label)
{
    ScratchRegisterScope scratch(*this);
    ma_dext(scratch, value.valueReg(), Imm32(0), Imm32(32));
    ma_b(scratch, scratch, label, b ? NonZero : Zero);
}

void
MacroAssembler::branchTestDouble(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    Condition actual = (cond == Equal) ? BelowOrEqual : Above;
    ma_b(tag, ImmTag(JSVAL_TAG_MAX_DOUBLE), label, actual);
}

void
MacroAssembler::branchTestDouble(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestDouble(cond, scratch2, label);
}

void
MacroAssembler::branchTestNumber(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestNumber(cond, scratch2, label);
}

void
MacroAssembler::branchTestBoolean(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestBoolean(cond, scratch2, label);
}

void
MacroAssembler::branchTestBooleanTruthy(bool b, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    unboxBoolean(value, scratch2);
    ma_b(scratch2, scratch2, label, b ? NonZero : Zero);
}

void
MacroAssembler::branchTestString(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestString(cond, scratch2, label);
}

void
MacroAssembler::branchTestStringTruthy(bool b, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    unboxString(value, scratch2);
    load32(Address(scratch2, JSString::offsetOfLength()), scratch2);
    ma_b(scratch2, Imm32(0), label, b ? NotEqual : Equal);
}

void
MacroAssembler::branchTestSymbol(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestSymbol(cond, scratch2, label);
}

void
MacroAssembler::branchTestNull(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestNull(cond, scratch2, label);
}

void
MacroAssembler::branchTestObject(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestObject(cond, scratch2, label);
}

void
MacroAssembler::branchTestPrimitive(Condition cond, const ValueOperand& value, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    branchTestPrimitive(cond, scratch2, label);
}

template <class L>
void
MacroAssembler::branchTestMagic(Condition cond, const ValueOperand& value, L label)
{
    SecondScratchRegisterScope scratch2(*this);
    splitTag(value, scratch2);
    ma_b(scratch2, ImmTag(JSVAL_TAG_MAGIC), label, cond);
}

void
MacroAssembler::branchTestMagic(Condition cond, const Address& valaddr, JSWhyMagic why, Label* label)
{
    uint64_t magic = MagicValue(why).asRawBits();
    SecondScratchRegisterScope scratch(*this);
    loadPtr(valaddr, scratch);
    ma_b(scratch, ImmWord(magic), label, cond);
}

void
MacroAssembler::branchTruncateDoubleMaybeModUint32(FloatRegister src, Register dest, Label* fail)
{
    as_truncld(ScratchDoubleReg, src);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromDouble(ScratchDoubleReg, dest);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_b(ScratchRegister, Imm32(0), fail, Assembler::NotEqual);

    as_sll(dest, dest, 0);
}

void
MacroAssembler::branchTruncateFloat32MaybeModUint32(FloatRegister src, Register dest, Label* fail)
{
    as_truncls(ScratchDoubleReg, src);
    as_cfc1(ScratchRegister, Assembler::FCSR);
    moveFromDouble(ScratchDoubleReg, dest);
    ma_ext(ScratchRegister, ScratchRegister, Assembler::CauseV, 1);
    ma_b(ScratchRegister, Imm32(0), fail, Assembler::NotEqual);

    as_sll(dest, dest, 0);
}

//}}} check_macroassembler_style
// ===============================================================

// The specializations for cmpPtrSet are outside the braces because check_macroassembler_style can't yet
// deal with specializations.

template<>
inline void
MacroAssembler::cmpPtrSet(Assembler::Condition cond, Address lhs, ImmPtr rhs,
                          Register dest)
{
    loadPtr(lhs, SecondScratchReg);
    cmpPtrSet(cond, SecondScratchReg, rhs, dest);
}

template<>
inline void
MacroAssembler::cmpPtrSet(Assembler::Condition cond, Register lhs, Address rhs,
                          Register dest)
{
    loadPtr(rhs, ScratchRegister);
    cmpPtrSet(cond, lhs, ScratchRegister, dest);
}

template<>
inline void
MacroAssembler::cmp32Set(Assembler::Condition cond, Register lhs, Address rhs,
                         Register dest)
{
    load32(rhs, ScratchRegister);
    cmp32Set(cond, lhs, ScratchRegister, dest);
}

void
MacroAssemblerPPC64LECompat::incrementInt32Value(const Address& addr)
{
    asMasm().add32(Imm32(1), addr);
}

void
MacroAssemblerPPC64LECompat::computeEffectiveAddress(const BaseIndex& address, Register dest)
{
    computeScaledAddress(address, dest);
    if (address.offset)
        asMasm().addPtr(Imm32(address.offset), dest);
}

void
MacroAssemblerPPC64LECompat::retn(Imm32 n)
{
    // pc <- [sp]; sp += n
    loadPtr(Address(StackPointer, 0), ra);
    asMasm().addPtr(n, StackPointer);
    as_jr(ra);
    as_nop();
}

void
MacroAssembler::moveFloat32ToGPR(FloatRegister src, Register dest)
{
    moveFromFloat32(src, dest);
}

void
MacroAssembler::moveGPRToFloat32(Register src, FloatRegister dest)
{
    moveToFloat32(src, dest);
}

void
MacroAssembler::move8SignExtend(Register src, Register dest)
{
    ma_seb(dest, src);
}

void
MacroAssembler::move16SignExtend(Register src, Register dest)
{
    ma_seh(dest, src);
}

// ===============================================================
// Logical instructions

void
MacroAssembler::not32(Register reg)
{
    ma_not(reg, reg);
}

void
MacroAssembler::and32(Register src, Register dest)
{
    as_and(dest, dest, src);
}

void
MacroAssembler::and32(Imm32 imm, Register dest)
{
    ma_and(dest, imm);
}

void
MacroAssembler::and32(Imm32 imm, const Address& dest)
{
    load32(dest, SecondScratchReg);
    ma_and(SecondScratchReg, imm);
    store32(SecondScratchReg, dest);
}

void
MacroAssembler::and32(const Address& src, Register dest)
{
    load32(src, SecondScratchReg);
    ma_and(dest, SecondScratchReg);
}

void
MacroAssembler::or32(Register src, Register dest)
{
    ma_or(dest, src);
}

void
MacroAssembler::or32(Imm32 imm, Register dest)
{
    ma_or(dest, imm);
}

void
MacroAssembler::or32(Imm32 imm, const Address& dest)
{
    load32(dest, SecondScratchReg);
    ma_or(SecondScratchReg, imm);
    store32(SecondScratchReg, dest);
}

void
MacroAssembler::xor32(Register src, Register dest)
{
    ma_xor(dest, src);
}

void
MacroAssembler::xor32(Imm32 imm, Register dest)
{
    ma_xor(dest, imm);
}

// ===============================================================
// Arithmetic instructions

void
MacroAssembler::add32(Register src, Register dest)
{
    as_addu(dest, dest, src);
}

void
MacroAssembler::add32(Imm32 imm, Register dest)
{
    ma_addu(dest, dest, imm);
}

void
MacroAssembler::add32(Imm32 imm, const Address& dest)
{
    load32(dest, SecondScratchReg);
    ma_addu(SecondScratchReg, imm);
    store32(SecondScratchReg, dest);
}

void
MacroAssembler::addPtr(Imm32 imm, const Address& dest)
{
    loadPtr(dest, ScratchRegister);
    addPtr(imm, ScratchRegister);
    storePtr(ScratchRegister, dest);
}

void
MacroAssembler::addPtr(const Address& src, Register dest)
{
    loadPtr(src, ScratchRegister);
    addPtr(ScratchRegister, dest);
}

void
MacroAssembler::addDouble(FloatRegister src, FloatRegister dest)
{
    as_addd(dest, dest, src);
}

void
MacroAssembler::addFloat32(FloatRegister src, FloatRegister dest)
{
    as_adds(dest, dest, src);
}

void
MacroAssembler::sub32(Register src, Register dest)
{
    as_subu(dest, dest, src);
}

void
MacroAssembler::sub32(Imm32 imm, Register dest)
{
    ma_subu(dest, dest, imm);
}

void
MacroAssembler::sub32(const Address& src, Register dest)
{
    load32(src, SecondScratchReg);
    as_subu(dest, dest, SecondScratchReg);
}

void
MacroAssembler::subPtr(Register src, const Address& dest)
{
    loadPtr(dest, SecondScratchReg);
    subPtr(src, SecondScratchReg);
    storePtr(SecondScratchReg, dest);
}

void
MacroAssembler::subPtr(const Address& addr, Register dest)
{
    loadPtr(addr, SecondScratchReg);
    subPtr(SecondScratchReg, dest);
}

void
MacroAssembler::subDouble(FloatRegister src, FloatRegister dest)
{
    as_subd(dest, dest, src);
}

void
MacroAssembler::subFloat32(FloatRegister src, FloatRegister dest)
{
    as_subs(dest, dest, src);
}

void
MacroAssembler::mul32(Register rhs, Register srcDest)
{
    as_mul(srcDest, srcDest, rhs);
}

void
MacroAssembler::mulFloat32(FloatRegister src, FloatRegister dest)
{
    as_muls(dest, dest, src);
}

void
MacroAssembler::mulDouble(FloatRegister src, FloatRegister dest)
{
    as_muld(dest, dest, src);
}

void
MacroAssembler::mulDoublePtr(ImmPtr imm, Register temp, FloatRegister dest)
{
    movePtr(imm, ScratchRegister);
    loadDouble(Address(ScratchRegister, 0), ScratchDoubleReg);
    mulDouble(ScratchDoubleReg, dest);
}

void
MacroAssembler::quotient32(Register rhs, Register srcDest, bool isUnsigned)
{
    if (isUnsigned)
        as_divu(srcDest, rhs);
    else
        as_div(srcDest, rhs);
    as_mflo(srcDest);
}

void
MacroAssembler::remainder32(Register rhs, Register srcDest, bool isUnsigned)
{
    if (isUnsigned)
        as_divu(srcDest, rhs);
    else
        as_div(srcDest, rhs);
    as_mfhi(srcDest);
}

void
MacroAssembler::divFloat32(FloatRegister src, FloatRegister dest)
{
    as_divs(dest, dest, src);
}

void
MacroAssembler::divDouble(FloatRegister src, FloatRegister dest)
{
    as_divd(dest, dest, src);
}

void
MacroAssembler::neg32(Register reg)
{
    ma_negu(reg, reg);
}

void
MacroAssembler::negateDouble(FloatRegister reg)
{
    as_negd(reg, reg);
}

void
MacroAssembler::negateFloat(FloatRegister reg)
{
    as_negs(reg, reg);
}

void
MacroAssembler::absFloat32(FloatRegister src, FloatRegister dest)
{
    as_abss(dest, src);
}

void
MacroAssembler::absDouble(FloatRegister src, FloatRegister dest)
{
    as_absd(dest, src);
}

void
MacroAssembler::sqrtFloat32(FloatRegister src, FloatRegister dest)
{
    as_sqrts(dest, src);
}

void
MacroAssembler::sqrtDouble(FloatRegister src, FloatRegister dest)
{
    as_sqrtd(dest, src);
}

void
MacroAssembler::minFloat32(FloatRegister other, FloatRegister srcDest, bool handleNaN)
{
    minMaxFloat32(srcDest, other, handleNaN, false);
}

void
MacroAssembler::minDouble(FloatRegister other, FloatRegister srcDest, bool handleNaN)
{
    minMaxDouble(srcDest, other, handleNaN, false);
}

void
MacroAssembler::maxFloat32(FloatRegister other, FloatRegister srcDest, bool handleNaN)
{
    minMaxFloat32(srcDest, other, handleNaN, true);
}

void
MacroAssembler::maxDouble(FloatRegister other, FloatRegister srcDest, bool handleNaN)
{
    minMaxDouble(srcDest, other, handleNaN, true);
}

// ===============================================================
// Shift functions

void
MacroAssembler::lshift32(Register src, Register dest)
{
    ma_sll(dest, dest, src);
}

void
MacroAssembler::lshift32(Imm32 imm, Register dest)
{
    ma_sll(dest, dest, imm);
}

void
MacroAssembler::rshift32(Register src, Register dest)
{
    ma_srl(dest, dest, src);
}

void
MacroAssembler::rshift32(Imm32 imm, Register dest)
{
    ma_srl(dest, dest, imm);
}

void
MacroAssembler::rshift32Arithmetic(Register src, Register dest)
{
    ma_sra(dest, dest, src);
}

void
MacroAssembler::rshift32Arithmetic(Imm32 imm, Register dest)
{
    ma_sra(dest, dest, imm);
}

// ===============================================================
// Rotation functions
void
MacroAssembler::rotateLeft(Imm32 count, Register input, Register dest)
{
    if (count.value)
        ma_rol(dest, input, count);
    else
        ma_move(dest, input);
}
void
MacroAssembler::rotateLeft(Register count, Register input, Register dest)
{
    ma_rol(dest, input, count);
}
void
MacroAssembler::rotateRight(Imm32 count, Register input, Register dest)
{
    if (count.value)
        ma_ror(dest, input, count);
    else
        ma_move(dest, input);
}
void
MacroAssembler::rotateRight(Register count, Register input, Register dest)
{
    ma_ror(dest, input, count);
}

// ===============================================================
// Bit counting functions

void
MacroAssembler::clz32(Register src, Register dest, bool knownNotZero)
{
    as_clz(dest, src);
}

void
MacroAssembler::ctz32(Register src, Register dest, bool knownNotZero)
{
    ma_ctz(dest, src);
}

void
MacroAssembler::popcnt32(Register input,  Register output, Register tmp)
{
    // Equivalent to GCC output of mozilla::CountPopulation32()
    ma_move(output, input);
    ma_sra(tmp, input, Imm32(1));
    ma_and(tmp, Imm32(0x55555555));
    ma_subu(output, tmp);
    ma_sra(tmp, output, Imm32(2));
    ma_and(output, Imm32(0x33333333));
    ma_and(tmp, Imm32(0x33333333));
    ma_addu(output, tmp);
    ma_srl(tmp, output, Imm32(4));
    ma_addu(output, tmp);
    ma_and(output, Imm32(0xF0F0F0F));
    ma_sll(tmp, output, Imm32(8));
    ma_addu(output, tmp);
    ma_sll(tmp, output, Imm32(16));
    ma_addu(output, tmp);
    ma_sra(output, output, Imm32(24));
}

// ===============================================================
// Branch functions

template <class L>
void
MacroAssembler::branch32(Condition cond, Register lhs, Register rhs, L label)
{
    ma_b(lhs, rhs, label, cond);
}

template <class L>
void
MacroAssembler::branch32(Condition cond, Register lhs, Imm32 imm, L label)
{
    ma_b(lhs, imm, label, cond);
}

void
MacroAssembler::branch32(Condition cond, const Address& lhs, Register rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    ma_b(SecondScratchReg, rhs, label, cond);
}

void
MacroAssembler::branch32(Condition cond, const Address& lhs, Imm32 rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    ma_b(SecondScratchReg, rhs, label, cond);
}

void
MacroAssembler::branch32(Condition cond, const AbsoluteAddress& lhs, Register rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    ma_b(SecondScratchReg, rhs, label, cond);
}

void
MacroAssembler::branch32(Condition cond, const AbsoluteAddress& lhs, Imm32 rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    ma_b(SecondScratchReg, rhs, label, cond);
}

void
MacroAssembler::branch32(Condition cond, const BaseIndex& lhs, Imm32 rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    ma_b(SecondScratchReg, rhs, label, cond);
}

void
MacroAssembler::branch32(Condition cond, wasm::SymbolicAddress addr, Imm32 imm, Label* label)
{
    load32(addr, SecondScratchReg);
    ma_b(SecondScratchReg, imm, label, cond);
}

template <class L>
void
MacroAssembler::branchPtr(Condition cond, Register lhs, Register rhs, L label)
{
    ma_b(lhs, rhs, label, cond);
}

void
MacroAssembler::branchPtr(Condition cond, Register lhs, Imm32 rhs, Label* label)
{
    ma_b(lhs, rhs, label, cond);
}

void
MacroAssembler::branchPtr(Condition cond, Register lhs, ImmPtr rhs, Label* label)
{
    ma_b(lhs, rhs, label, cond);
}

void
MacroAssembler::branchPtr(Condition cond, Register lhs, ImmGCPtr rhs, Label* label)
{
    ma_b(lhs, rhs, label, cond);
}

void
MacroAssembler::branchPtr(Condition cond, Register lhs, ImmWord rhs, Label* label)
{
    ma_b(lhs, rhs, label, cond);
}

template <class L>
void
MacroAssembler::branchPtr(Condition cond, const Address& lhs, Register rhs, L label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, const Address& lhs, ImmPtr rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, const Address& lhs, ImmGCPtr rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, const Address& lhs, ImmWord rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, const AbsoluteAddress& lhs, Register rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, const AbsoluteAddress& lhs, ImmWord rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, wasm::SymbolicAddress lhs, Register rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchPtr(Condition cond, const BaseIndex& lhs, ImmWord rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchFloat(DoubleCondition cond, FloatRegister lhs, FloatRegister rhs,
                            Label* label)
{
    ma_bc1s(lhs, rhs, label, cond);
}

void
MacroAssembler::branchTruncateFloat32ToInt32(FloatRegister src, Register dest, Label* fail)
{
    MOZ_CRASH();
}

void
MacroAssembler::branchDouble(DoubleCondition cond, FloatRegister lhs, FloatRegister rhs,
                             Label* label)
{
    ma_bc1d(lhs, rhs, label, cond);
}

void
MacroAssembler::branchTruncateDoubleToInt32(FloatRegister src, Register dest, Label* fail)
{
    MOZ_CRASH();
}

template <typename T>
void
MacroAssembler::branchAdd32(Condition cond, T src, Register dest, Label* overflow)
{
    switch (cond) {
      case Overflow:
        ma_addTestOverflow(dest, dest, src, overflow);
        break;
      case CarryClear:
      case CarrySet:
        ma_addTestCarry(cond, dest, dest, src, overflow);
        break;
      default:
        MOZ_CRASH("NYI");
    }
}

template <typename T>
void
MacroAssembler::branchSub32(Condition cond, T src, Register dest, Label* overflow)
{
    switch (cond) {
      case Overflow:
        ma_subTestOverflow(dest, dest, src, overflow);
        break;
      case NonZero:
      case Zero:
        ma_subu(dest, src);
        ma_b(dest, dest, overflow, cond);
        break;
      default:
        MOZ_CRASH("NYI");
    }
}

void
MacroAssembler::decBranchPtr(Condition cond, Register lhs, Imm32 rhs, Label* label)
{
    subPtr(rhs, lhs);
    branchPtr(cond, lhs, Imm32(0), label);
}

template <class L>
void
MacroAssembler::branchTest32(Condition cond, Register lhs, Register rhs, L label)
{
    MOZ_ASSERT(cond == Zero || cond == NonZero || cond == Signed || cond == NotSigned);
    if (lhs == rhs) {
        ma_b(lhs, rhs, label, cond);
    } else {
        as_and(ScratchRegister, lhs, rhs);
        ma_b(ScratchRegister, ScratchRegister, label, cond);
    }
}

template <class L>
void
MacroAssembler::branchTest32(Condition cond, Register lhs, Imm32 rhs, L label)
{
    MOZ_ASSERT(cond == Zero || cond == NonZero || cond == Signed || cond == NotSigned);
    ma_and(ScratchRegister, lhs, rhs);
    ma_b(ScratchRegister, ScratchRegister, label, cond);
}

void
MacroAssembler::branchTest32(Condition cond, const Address& lhs, Imm32 rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    branchTest32(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchTest32(Condition cond, const AbsoluteAddress& lhs, Imm32 rhs, Label* label)
{
    load32(lhs, SecondScratchReg);
    branchTest32(cond, SecondScratchReg, rhs, label);
}

template <class L>
void
MacroAssembler::branchTestPtr(Condition cond, Register lhs, Register rhs, L label)
{
    MOZ_ASSERT(cond == Zero || cond == NonZero || cond == Signed || cond == NotSigned);
    if (lhs == rhs) {
        ma_b(lhs, rhs, label, cond);
    } else {
        as_and(ScratchRegister, lhs, rhs);
        ma_b(ScratchRegister, ScratchRegister, label, cond);
    }
}

void
MacroAssembler::branchTestPtr(Condition cond, Register lhs, Imm32 rhs, Label* label)
{
    MOZ_ASSERT(cond == Zero || cond == NonZero || cond == Signed || cond == NotSigned);
    ma_and(ScratchRegister, lhs, rhs);
    ma_b(ScratchRegister, ScratchRegister, label, cond);
}

void
MacroAssembler::branchTestPtr(Condition cond, const Address& lhs, Imm32 rhs, Label* label)
{
    loadPtr(lhs, SecondScratchReg);
    branchTestPtr(cond, SecondScratchReg, rhs, label);
}

void
MacroAssembler::branchTestUndefined(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_UNDEFINED), label, cond);
}

void
MacroAssembler::branchTestUndefined(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestUndefined(cond, scratch2, label);
}

void
MacroAssembler::branchTestUndefined(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestUndefined(cond, scratch2, label);
}

void
MacroAssembler::branchTestInt32(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_INT32), label, cond);
}

void
MacroAssembler::branchTestInt32(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestInt32(cond, scratch2, label);
}

void
MacroAssembler::branchTestInt32(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestInt32(cond, scratch2, label);
}

void
MacroAssembler::branchTestDouble(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestDouble(cond, scratch2, label);
}

void
MacroAssembler::branchTestDouble(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestDouble(cond, scratch2, label);
}

void
MacroAssembler::branchTestDoubleTruthy(bool b, FloatRegister value, Label* label)
{
    ma_lid(ScratchDoubleReg, 0.0);
    DoubleCondition cond = b ? DoubleNotEqual : DoubleEqualOrUnordered;
    ma_bc1d(value, ScratchDoubleReg, label, cond);
}

void
MacroAssembler::branchTestNumber(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    Condition actual = cond == Equal ? BelowOrEqual : Above;
    ma_b(tag, ImmTag(JSVAL_UPPER_INCL_TAG_OF_NUMBER_SET), label, actual);
}

void
MacroAssembler::branchTestBoolean(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_BOOLEAN), label, cond);
}

void
MacroAssembler::branchTestBoolean(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestBoolean(cond, scratch2, label);
}

void
MacroAssembler::branchTestBoolean(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestBoolean(cond, scratch2, label);
}

void
MacroAssembler::branchTestString(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_STRING), label, cond);
}

void
MacroAssembler::branchTestString(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestString(cond, scratch2, label);
}

void
MacroAssembler::branchTestString(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestString(cond, scratch2, label);
}

void
MacroAssembler::branchTestSymbol(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_SYMBOL), label, cond);
}

void
MacroAssembler::branchTestSymbol(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestSymbol(cond, scratch2, label);
}

void
MacroAssembler::branchTestNull(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_NULL), label, cond);
}

void
MacroAssembler::branchTestNull(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestNull(cond, scratch2, label);
}

void
MacroAssembler::branchTestNull(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestNull(cond, scratch2, label);
}

void
MacroAssembler::branchTestObject(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_OBJECT), label, cond);
}

void
MacroAssembler::branchTestObject(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestObject(cond, scratch2, label);
}

void
MacroAssembler::branchTestObject(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestObject(cond, scratch2, label);
}

void
MacroAssembler::branchTestGCThing(Condition cond, const Address& address, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    ma_b(scratch2, ImmTag(JSVAL_LOWER_INCL_TAG_OF_GCTHING_SET), label,
         (cond == Equal) ? AboveOrEqual : Below);
}
void
MacroAssembler::branchTestGCThing(Condition cond, const BaseIndex& address, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    ma_b(scratch2, ImmTag(JSVAL_LOWER_INCL_TAG_OF_GCTHING_SET), label,
         (cond == Equal) ? AboveOrEqual : Below);
}

void
MacroAssembler::branchTestPrimitive(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_UPPER_EXCL_TAG_OF_PRIMITIVE_SET), label,
         (cond == Equal) ? Below : AboveOrEqual);
}

void
MacroAssembler::branchTestMagic(Condition cond, Register tag, Label* label)
{
    MOZ_ASSERT(cond == Equal || cond == NotEqual);
    ma_b(tag, ImmTag(JSVAL_TAG_MAGIC), label, cond);
}

void
MacroAssembler::branchTestMagic(Condition cond, const Address& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestMagic(cond, scratch2, label);
}

void
MacroAssembler::branchTestMagic(Condition cond, const BaseIndex& address, Label* label)
{
    SecondScratchRegisterScope scratch2(*this);
    extractTag(address, scratch2);
    branchTestMagic(cond, scratch2, label);
}

void
MacroAssembler::branchToComputedAddress(const BaseIndex& addr)
{
    loadPtr(addr, ScratchRegister);
    branch(ScratchRegister);
}

void
MacroAssembler::cmp32Move32(Condition cond, Register lhs, Register rhs, Register src,
                            Register dest)
{
    MOZ_CRASH();
}

void
MacroAssembler::cmp32MovePtr(Condition cond, Register lhs, Imm32 rhs, Register src,
                             Register dest)
{
    MOZ_CRASH();
}

void
MacroAssembler::cmp32Move32(Condition cond, Register lhs, const Address& rhs, Register src,
                            Register dest)
{
    MOZ_CRASH();
}

void
MacroAssembler::test32LoadPtr(Condition cond, const Address& addr, Imm32 mask, const Address& src,
                              Register dest)
{
    MOZ_RELEASE_ASSERT(!JitOptions.spectreStringMitigations);
    Label skip;
    branchTest32(Assembler::InvertCondition(cond), addr, mask, &skip);
    loadPtr(src, dest);
    bind(&skip);
}

void
MacroAssembler::test32MovePtr(Condition cond, const Address& addr, Imm32 mask, Register src,
                              Register dest)
{
    MOZ_CRASH();
}

void
MacroAssembler::spectreBoundsCheck32(Register index, Register length, Register maybeScratch,
                                     Label* failure)
{
    MOZ_RELEASE_ASSERT(!JitOptions.spectreIndexMasking);
    branch32(Assembler::BelowOrEqual, length, index, failure);
}

void
MacroAssembler::spectreBoundsCheck32(Register index, const Address& length, Register maybeScratch,
                                     Label* failure)
{
    MOZ_RELEASE_ASSERT(!JitOptions.spectreIndexMasking);
    branch32(Assembler::BelowOrEqual, length, index, failure);
}

void
MacroAssembler::spectreMovePtr(Condition cond, Register src, Register dest)
{
    MOZ_CRASH();
}

void
MacroAssembler::spectreZeroRegister(Condition cond, Register scratch, Register dest)
{
    MOZ_CRASH();
}

// ========================================================================
// Memory access primitives.
void
MacroAssembler::storeFloat32x3(FloatRegister src, const Address& dest)
{
    MOZ_CRASH("NYI");
}
void
MacroAssembler::storeFloat32x3(FloatRegister src, const BaseIndex& dest)
{
    MOZ_CRASH("NYI");
}

void
MacroAssembler::storeUncanonicalizedDouble(FloatRegister src, const Address& addr)
{
    ma_sd(src, addr);
}
void
MacroAssembler::storeUncanonicalizedDouble(FloatRegister src, const BaseIndex& addr)
{
    ma_sd(src, addr);
}

void
MacroAssembler::storeUncanonicalizedFloat32(FloatRegister src, const Address& addr)
{
    ma_ss(src, addr);
}
void
MacroAssembler::storeUncanonicalizedFloat32(FloatRegister src, const BaseIndex& addr)
{
    ma_ss(src, addr);
}

void
MacroAssembler::memoryBarrier(MemoryBarrierBits barrier)
{
    as_sync();
}

// ===============================================================
// Clamping functions.

void
MacroAssembler::clampIntToUint8(Register reg)
{
    // If reg is < 0, then we want to clamp to 0.
    as_slti(ScratchRegister, reg, 0);
    as_movn(reg, zero, ScratchRegister);

    // If reg is >= 255, then we want to clamp to 255.
    ma_li(SecondScratchReg, Imm32(255));
    as_slti(ScratchRegister, reg, 255);
    as_movz(reg, SecondScratchReg, ScratchRegister);
}

//}}} check_macroassembler_style
// ===============================================================

} // namespace jit
} // namespace js

#endif /* jit_mips_shared_MacroAssembler_mips_shared_inl_h */
