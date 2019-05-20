/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

/* Code generator for little-endian 64-bit PowerPC compliant to Power ISA v3.0B. */

#include "jit/ppc64le/CodeGenerator-ppc64le.h"

#include "mozilla/DebugOnly.h"
#include "mozilla/MathAlgorithms.h"

#include "jsnum.h"

#include "jit/CodeGenerator.h"
#include "jit/JitFrames.h"
#include "jit/JitRealm.h"
#include "jit/MIR.h"
#include "jit/MIRGraph.h"
#include "js/Conversions.h"
#include "vm/JSContext.h"
#include "vm/Realm.h"
#include "vm/Shape.h"
#include "vm/TraceLogging.h"

#include "jit/MacroAssembler-inl.h"
#include "jit/shared/CodeGenerator-shared-inl.h"
#include "vm/JSScript-inl.h"

using namespace js;
using namespace js::jit;

using mozilla::DebugOnly;
using mozilla::FloorLog2;
using mozilla::NegativeInfinity;
using JS::GenericNaN;
using JS::ToInt32;

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

CodeGeneratorPPC64LE::CodeGeneratorPPC64LE(MIRGenerator* gen, LIRGraph* graph, MacroAssembler* masm)
  : CodeGeneratorShared(gen, graph, masm)
{
}

ValueOperand
CodeGeneratorPPC64LE::ToValue(LInstruction* ins, size_t pos)
{
    return ValueOperand(ToRegister(ins->getOperand(pos)));
}

ValueOperand
CodeGeneratorPPC64LE::ToTempValue(LInstruction* ins, size_t pos)
{
    return ValueOperand(ToRegister(ins->getTemp(pos)));
}

void
CodeGenerator::visitBox(LBox* box)
{
    ADBlock();
    const LAllocation* in = box->getOperand(0);
    const LDefinition* result = box->getDef(0);

    if (IsFloatingPointType(box->type())) {
        FloatRegister reg = ToFloatRegister(in);
        if (box->type() == MIRType::Float32) {
            masm.convertFloat32ToDouble(reg, ScratchDoubleReg);
            reg = ScratchDoubleReg;
        }
        masm.moveFromDouble(reg, ToRegister(result));
    } else {
        masm.boxValue(ValueTypeFromMIRType(box->type()), ToRegister(in), ToRegister(result));
    }
}

void
CodeGenerator::visitUnbox(LUnbox* unbox)
{
    ADBlock();
    MUnbox* mir = unbox->mir();

    if (mir->fallible()) {
        const ValueOperand value = ToValue(unbox, LUnbox::Input);
        masm.splitTag(value, SecondScratchReg);
        bailoutCmp32(Assembler::NotEqual, SecondScratchReg, Imm32(MIRTypeToTag(mir->type())),
                     unbox->snapshot());
    }

    LAllocation* input = unbox->getOperand(LUnbox::Input);
    Register result = ToRegister(unbox->output());
    if (input->isRegister()) {
        Register inputReg = ToRegister(input);
        switch (mir->type()) {
          case MIRType::Int32:
            masm.unboxInt32(inputReg, result);
            break;
          case MIRType::Boolean:
            masm.unboxBoolean(inputReg, result);
            break;
          case MIRType::Object:
            masm.unboxObject(inputReg, result);
            break;
          case MIRType::String:
            masm.unboxString(inputReg, result);
            break;
          case MIRType::Symbol:
            masm.unboxSymbol(inputReg, result);
            break;
          default:
            MOZ_CRASH("Given MIRType cannot be unboxed.");
        }
        return;
    }

    Address inputAddr = ToAddress(input);
    switch (mir->type()) {
      case MIRType::Int32:
        masm.unboxInt32(inputAddr, result);
        break;
      case MIRType::Boolean:
        masm.unboxBoolean(inputAddr, result);
        break;
      case MIRType::Object:
        masm.unboxObject(inputAddr, result);
        break;
      case MIRType::String:
        masm.unboxString(inputAddr, result);
        break;
      case MIRType::Symbol:
        masm.unboxSymbol(inputAddr, result);
        break;
      default:
        MOZ_CRASH("Given MIRType cannot be unboxed.");
    }
}

void
CodeGeneratorPPC64LE::splitTagForTest(const ValueOperand& value, ScratchTagScope& tag)
{
    masm.splitTag(value.valueReg(), tag);
}

void
CodeGenerator::visitCompareB(LCompareB* lir)
{
    ADBlock();
    MCompare* mir = lir->mir();

    const ValueOperand lhs = ToValue(lir, LCompareB::Lhs);
    const LAllocation* rhs = lir->rhs();
    const Register output = ToRegister(lir->output());

    MOZ_ASSERT(mir->jsop() == JSOP_STRICTEQ || mir->jsop() == JSOP_STRICTNE);
    Assembler::Condition cond = JSOpToCondition(mir->compareType(), mir->jsop());

    // Load boxed boolean in ScratchRegister.
    if (rhs->isConstant())
        masm.moveValue(rhs->toConstant()->toJSValue(), ValueOperand(ScratchRegister));
    else
        masm.boxValue(JSVAL_TYPE_BOOLEAN, ToRegister(rhs), ScratchRegister);

    // Perform the comparison.
    masm.cmpPtrSet(cond, lhs.valueReg(), ScratchRegister, output);
}

void
CodeGenerator::visitCompareBAndBranch(LCompareBAndBranch* lir)
{
    ADBlock();
    MCompare* mir = lir->cmpMir();
    const ValueOperand lhs = ToValue(lir, LCompareBAndBranch::Lhs);
    const LAllocation* rhs = lir->rhs();

    MOZ_ASSERT(mir->jsop() == JSOP_STRICTEQ || mir->jsop() == JSOP_STRICTNE);

    // Load boxed boolean in ScratchRegister.
    if (rhs->isConstant())
        masm.moveValue(rhs->toConstant()->toJSValue(), ValueOperand(ScratchRegister));
    else
        masm.boxValue(JSVAL_TYPE_BOOLEAN, ToRegister(rhs), ScratchRegister);

    // Perform the comparison.
    Assembler::Condition cond = JSOpToCondition(mir->compareType(), mir->jsop());
    emitBranch(lhs.valueReg(), ScratchRegister, cond, lir->ifTrue(), lir->ifFalse());
}

void
CodeGenerator::visitCompareBitwise(LCompareBitwise* lir)
{
    ADBlock();
    MCompare* mir = lir->mir();
    Assembler::Condition cond = JSOpToCondition(mir->compareType(), mir->jsop());
    const ValueOperand lhs = ToValue(lir, LCompareBitwise::LhsInput);
    const ValueOperand rhs = ToValue(lir, LCompareBitwise::RhsInput);
    const Register output = ToRegister(lir->output());

    MOZ_ASSERT(IsEqualityOp(mir->jsop()));

    masm.cmpPtrSet(cond, lhs.valueReg(), rhs.valueReg(), output);
}

void
CodeGenerator::visitCompareBitwiseAndBranch(LCompareBitwiseAndBranch* lir)
{
    ADBlock();
    MCompare* mir = lir->cmpMir();
    Assembler::Condition cond = JSOpToCondition(mir->compareType(), mir->jsop());
    const ValueOperand lhs = ToValue(lir, LCompareBitwiseAndBranch::LhsInput);
    const ValueOperand rhs = ToValue(lir, LCompareBitwiseAndBranch::RhsInput);

    MOZ_ASSERT(mir->jsop() == JSOP_EQ || mir->jsop() == JSOP_STRICTEQ ||
               mir->jsop() == JSOP_NE || mir->jsop() == JSOP_STRICTNE);

    emitBranch(lhs.valueReg(), rhs.valueReg(), cond, lir->ifTrue(), lir->ifFalse());
}

void
CodeGenerator::visitCompareI64(LCompareI64* lir)
{
    ADBlock();
    MCompare* mir = lir->mir();
    MOZ_ASSERT(mir->compareType() == MCompare::Compare_Int64 ||
               mir->compareType() == MCompare::Compare_UInt64);

    const LInt64Allocation lhs = lir->getInt64Operand(LCompareI64::Lhs);
    const LInt64Allocation rhs = lir->getInt64Operand(LCompareI64::Rhs);
    Register lhsReg = ToRegister64(lhs).reg;
    Register output = ToRegister(lir->output());
    Register rhsReg;

    if (IsConstant(rhs)) {
        rhsReg = ScratchRegister;
        masm.ma_li(rhsReg, ImmWord(ToInt64(rhs)));
    } else {
        rhsReg = ToRegister64(rhs).reg;
    }

    bool isSigned = mir->compareType() == MCompare::Compare_Int64;
    masm.cmpPtrSet(JSOpToCondition(lir->jsop(), isSigned), lhsReg, rhsReg, output);
}

void
CodeGenerator::visitCompareI64AndBranch(LCompareI64AndBranch* lir)
{
    ADBlock();
    MCompare* mir = lir->cmpMir();
    MOZ_ASSERT(mir->compareType() == MCompare::Compare_Int64 ||
               mir->compareType() == MCompare::Compare_UInt64);

    const LInt64Allocation lhs = lir->getInt64Operand(LCompareI64::Lhs);
    const LInt64Allocation rhs = lir->getInt64Operand(LCompareI64::Rhs);
    Register lhsReg = ToRegister64(lhs).reg;
    Register rhsReg;

    if (IsConstant(rhs)) {
        rhsReg = ScratchRegister;
        masm.ma_li(rhsReg, ImmWord(ToInt64(rhs)));
    } else {
        rhsReg = ToRegister64(rhs).reg;
    }

    bool isSigned = mir->compareType() == MCompare::Compare_Int64;
    Assembler::Condition cond = JSOpToCondition(lir->jsop(), isSigned);
    emitBranch(lhsReg, rhsReg, cond, lir->ifTrue(), lir->ifFalse());
}

void
CodeGenerator::visitDivOrModI64(LDivOrModI64* lir)
{
    ADBlock();
    // divdo will automatically set the Overflow bit if INT64_MIN/-1 is
    // performed, or if we divide by zero, so we just bailout based on that.

    Label noOverflow, done;
    Register lhs = ToRegister(lir->lhs());
    Register rhs = ToRegister(lir->rhs());
    Register output = ToRegister(lir->output());

    // DIVIDE! AND! CONQUER!
    if (lir->snapshot()) {
        // If Overflow is set, we must bail out. But only do this if
        // there is a snapshot, because if there isn't, Ion already knows
        // this operation is infallible (and we can avoid checking
        // for overflow, which is slightly faster).
        masm.xs_li(output, 0);
        masm.xs_mtxer(output); // whack XER[SO]
        masm.as_divdo_rc(output, lhs, rhs); // T = A / B

        // Did we trap?
        masm.ma_bc(Assembler::NoSO, &noOverflow, ShortJump);
        // Yes. Determine how.
        MOZ_ASSERT(lir->canBeNegativeOverflow() || lir->canBeDivideByZero());
        if (lir->canBeNegativeOverflow()) {
            if (lir->canBeDivideByZero()) {
                Label notNegOne;

                masm.branchPtr(Assembler::NotEqual, rhs, ImmWord(-1), &notNegOne);
                // If rhs was -1, then the offending operation must have been
                // INT64_MIN/-1.
                if (lir->mir()->isMod())
                    masm.move32(Imm32(0), output);
                else
                    masm.wasmTrap(wasm::Trap::IntegerOverflow, lir->bytecodeOffset());
                masm.ma_b(&done, ShortJump);
                masm.bind(&notNegOne);
            } else {
                // Just trap, it's the only possible triggering condition.
                masm.wasmTrap(wasm::Trap::IntegerOverflow, lir->bytecodeOffset());
            }
        }
        if (lir->canBeDivideByZero()) {
            // Must have been divide by zero.
            masm.wasmTrap(wasm::Trap::IntegerDivideByZero, lir->bytecodeOffset());
        }
    } else {
        masm.as_divd(output, lhs, rhs);
    }

    masm.bind(&noOverflow);
    if (lir->mir()->isMod()) {
        // Recover the remainder.
        // We don't need to check overflow; we know it can't.
        masm.as_mulld(ScratchRegister, output, rhs);
        masm.as_subf(output, ScratchRegister, lhs); // T = B - A
    }

    masm.bind(&done);
}

void
CodeGenerator::visitUDivOrModI64(LUDivOrModI64* lir)
{
    // Simpler, because no -1 check.
    ADBlock();
    Register lhs = ToRegister(lir->lhs());
    Register rhs = ToRegister(lir->rhs());
    Register output = ToRegister(lir->output());
    LSnapshot* snap = lir->snapshot();
    Label noOverflow, done;

    if (snap) {
        masm.xs_li(output, 0);
        masm.xs_mtxer(output); // whack XER[SO]
        masm.as_divduo_rc(output, lhs, rhs); // T = A / B

        // Did we trap?
        masm.ma_bc(Assembler::NoSO, &noOverflow, ShortJump);
        // Yes. Only one way that can happen here.
        MOZ_ASSERT(lir->canBeDivideByZero());
        masm.wasmTrap(wasm::Trap::IntegerDivideByZero, lir->bytecodeOffset());
    } else {
        masm.as_divdu(output, lhs, rhs);
    }

    masm.bind(&noOverflow);
    if (lir->mir()->isMod()) {
        // Recover the remainder.
        // We don't need to check overflow; we know it can't.
        masm.as_mulld(ScratchRegister, output, rhs);
        masm.as_subf(output, ScratchRegister, lhs); // T = B - A
    }

    masm.bind(&done);
}

template <typename T>
void
CodeGeneratorPPC64LE::emitWasmLoadI64(T* lir)
{
    ADBlock();
    const MWasmLoad* mir = lir->mir();

    Register ptrScratch = InvalidReg;
    if(!lir->ptrCopy()->isBogusTemp()){
        ptrScratch = ToRegister(lir->ptrCopy());
    }

    if (IsUnaligned(mir->access())) {
        masm.wasmUnalignedLoadI64(mir->access(), HeapReg, ToRegister(lir->ptr()),
                                  ptrScratch, ToOutRegister64(lir), ToRegister(lir->getTemp(1)));
    } else {
        masm.wasmLoadI64(mir->access(), HeapReg, ToRegister(lir->ptr()), ptrScratch,
                         ToOutRegister64(lir));
    }
}

void
CodeGenerator::visitWasmLoadI64(LWasmLoadI64* lir)
{
    emitWasmLoadI64(lir);
}

void
CodeGenerator::visitWasmUnalignedLoadI64(LWasmUnalignedLoadI64* lir)
{
    emitWasmLoadI64(lir);
}

template <typename T>
void
CodeGeneratorPPC64LE::emitWasmStoreI64(T* lir)
{
    ADBlock();
    const MWasmStore* mir = lir->mir();

    Register ptrScratch = InvalidReg;
    if(!lir->ptrCopy()->isBogusTemp()){
        ptrScratch = ToRegister(lir->ptrCopy());
    }

    if (IsUnaligned(mir->access())) {
        masm.wasmUnalignedStoreI64(mir->access(), ToRegister64(lir->value()), HeapReg,
                                   ToRegister(lir->ptr()), ptrScratch, ToRegister(lir->getTemp(1)));
    } else {
        masm.wasmStoreI64(mir->access(), ToRegister64(lir->value()), HeapReg,
                          ToRegister(lir->ptr()), ptrScratch);
    }
}

void
CodeGenerator::visitWasmStoreI64(LWasmStoreI64* lir)
{
    emitWasmStoreI64(lir);
}

void
CodeGenerator::visitWasmUnalignedStoreI64(LWasmUnalignedStoreI64* lir)
{
    emitWasmStoreI64(lir);
}

void
CodeGenerator::visitWasmSelectI64(LWasmSelectI64* lir)
{
    ADBlock();
    MOZ_ASSERT(lir->mir()->type() == MIRType::Int64);

    Register cond = ToRegister(lir->condExpr());
    const LInt64Allocation falseExpr = lir->falseExpr();

    Register64 out = ToOutRegister64(lir);
    MOZ_ASSERT(ToRegister64(lir->trueExpr()) == out, "true expr is reused for input");

    if (falseExpr.value().isRegister()) {
        masm.as_cmpi(cond, 0);
        masm.as_isel(out.reg, out.reg, ToRegister(falseExpr.value()), 2); // CR0[EQ]
    } else {
        Label done;
        masm.ma_b(cond, cond, &done, Assembler::NonZero, ShortJump);
        masm.loadPtr(ToAddress(falseExpr.value()), out.reg);
        masm.bind(&done);
    }
}

void
CodeGenerator::visitWasmReinterpretFromI64(LWasmReinterpretFromI64* lir)
{
    ADBlock();
    MOZ_ASSERT(lir->mir()->type() == MIRType::Double);
    MOZ_ASSERT(lir->mir()->input()->type() == MIRType::Int64);

    // No GPR<->FPR moves, so spill to memory (no mffgpr/mftgpr
    // like POWER6 had, alas -- good times).
    masm.as_stdu(ToRegister(lir->input()), StackPointer, -2); // extend to -8
    masm.as_lfd(ToFloatRegister(lir->output()), StackPointer, 0);
    masm.as_addi(StackPointer, StackPointer, 8);
}

void
CodeGenerator::visitWasmReinterpretToI64(LWasmReinterpretToI64* lir)
{
    ADBlock();
    MOZ_ASSERT(lir->mir()->type() == MIRType::Int64);
    MOZ_ASSERT(lir->mir()->input()->type() == MIRType::Double);

    // Sigh.
    masm.as_stfdu(ToFloatRegister(lir->input()), StackPointer, -8);
    masm.as_ld(ToRegister(lir->input()), StackPointer, 0);
    masm.as_addi(StackPointer, StackPointer, 8);
}

void
CodeGenerator::visitExtendInt32ToInt64(LExtendInt32ToInt64* lir)
{
    ADBlock();
    const LAllocation* input = lir->getOperand(0);
    Register output = ToRegister(lir->output());
    Register inpreg = ToRegister(input);

    // If the value is unsigned, then we just copy the input
    // register; it automatically is promoted to 64 bits.
    // If the value is signed, then sign extend it.
    if (lir->mir()->isUnsigned()) {
        if (inpreg != output)
            masm.as_or(output, inpreg, inpreg);
    } else
        masm.as_extsw(output, inpreg);
}

void
CodeGenerator::visitWrapInt64ToInt32(LWrapInt64ToInt32* lir)
{
    ADBlock();
    const LAllocation* input = lir->getOperand(0);
    Register output = ToRegister(lir->output());

    if (lir->mir()->bottomHalf()) {
        if (input->isMemory())
            masm.load32(ToAddress(input), output); // endian!
        else
            masm.as_rldicl(output, ToRegister(input), 0, 32);
    } else {
        MOZ_CRASH("Not implemented.");
        // but it would be rldicl rA,rS,32,32 (don't tell anyone, k?)
    }
}

void
CodeGenerator::visitSignExtendInt64(LSignExtendInt64* lir)
{
    ADBlock();
    Register64 input = ToRegister64(lir->getInt64Operand(0));
    Register64 output = ToOutRegister64(lir);
    switch (lir->mode()) {
      case MSignExtendInt64::Byte:
        masm.move32To64SignExtend(input.reg, output);
        masm.move8SignExtend(output.reg, output.reg);
        break;
      case MSignExtendInt64::Half:
        masm.move32To64SignExtend(input.reg, output);
        masm.move16SignExtend(output.reg, output.reg);
        break;
      case MSignExtendInt64::Word:
        masm.move32To64SignExtend(input.reg, output);
        break;
    }
}

void
CodeGenerator::visitClzI64(LClzI64* lir)
{
    ADBlock();
    Register64 input = ToRegister64(lir->getInt64Operand(0));
    Register64 output = ToOutRegister64(lir);
    masm.as_cntlzd(output.reg, input);
}

void
CodeGenerator::visitCtzI64(LCtzI64* lir)
{
    ADBlock();
    Register64 input = ToRegister64(lir->getInt64Operand(0));
    Register64 output = ToOutRegister64(lir);
    // Damn, it's good to be a POWER9 gangsta. When I was a boy,
    // we had to count our trailing zeroes on my G5 walking
    // uphill in the snow BOTH WAYS. We even have that fancy
    // population count instruction now. You kids have it so good.
    masm.as_cnttzd(output.reg, input);
}

void
CodeGenerator::visitNotI64(LNotI64* lir)
{
    ADBlock();
    Register64 input = ToRegister64(lir->getInt64Operand(0));
    Register output = ToRegister(lir->output());

    masm.cmp64Set(Assembler::Equal, input.reg, Imm32(0), output);
}

void
CodeGenerator::visitWasmTruncateToInt64(LWasmTruncateToInt64* lir)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(lir->input());
    Register64 output = ToOutRegister64(lir);

    MWasmTruncateToInt64* mir = lir->mir();
    MIRType fromType = mir->input()->type();

    MOZ_ASSERT(fromType == MIRType::Double || fromType == MIRType::Float32);

    auto* ool = new (alloc()) OutOfLineWasmTruncateCheck(mir, input, output);
    addOutOfLineCode(ool, mir);

    Label* oolEntry = ool->entry();
    Label* oolRejoin = ool->rejoin();
    bool isSaturating = mir->isSaturating();

    if (fromType == MIRType::Double) {
        if (mir->isUnsigned())
            masm.wasmTruncateDoubleToUInt64(input, output, isSaturating, oolEntry, oolRejoin,
                                            InvalidFloatReg);
        else
            masm.wasmTruncateDoubleToInt64(input, output, isSaturating, oolEntry, oolRejoin,
                                           InvalidFloatReg);
    } else {
        if (mir->isUnsigned())
            masm.wasmTruncateFloat32ToUInt64(input, output, isSaturating, oolEntry, oolRejoin,
                                             InvalidFloatReg);
        else
            masm.wasmTruncateFloat32ToInt64(input, output, isSaturating, oolEntry, oolRejoin,
                                            InvalidFloatReg);
    }
}

void
CodeGenerator::visitInt64ToFloatingPoint(LInt64ToFloatingPoint* lir)
{
    ADBlock();
    Register64 input = ToRegister64(lir->getInt64Operand(0));
    FloatRegister output = ToFloatRegister(lir->output());

    MIRType outputType = lir->mir()->type();
    MOZ_ASSERT(outputType == MIRType::Double || outputType == MIRType::Float32);

    if (outputType == MIRType::Double) {
        if (lir->mir()->isUnsigned())
            masm.convertUInt64ToDouble(input, output, Register::Invalid());
        else
            masm.convertInt64ToDouble(input, output);
    } else {
        if (lir->mir()->isUnsigned())
            masm.convertUInt64ToFloat32(input, output, Register::Invalid());
        else
            masm.convertInt64ToFloat32(input, output);
    }
}

void
CodeGenerator::visitTestI64AndBranch(LTestI64AndBranch* lir)
{
    ADBlock();
    Register64 input = ToRegister64(lir->getInt64Operand(0));
    MBasicBlock* ifTrue = lir->ifTrue();
    MBasicBlock* ifFalse = lir->ifFalse();

    emitBranch(input.reg, Imm32(0), Assembler::NonZero, ifTrue, ifFalse);
}

Operand
CodeGeneratorPPC64LE::ToOperand(const LAllocation& a)
{
    if (a.isGeneralReg())
        return Operand(a.toGeneralReg()->reg());
    if (a.isFloatReg())
        return Operand(a.toFloatReg()->reg());
    return Operand(masm.getStackPointer(), ToStackOffset(&a));
}

Operand
CodeGeneratorPPC64LE::ToOperand(const LAllocation* a)
{
    return ToOperand(*a);
}

Operand
CodeGeneratorPPC64LE::ToOperand(const LDefinition* def)
{
    return ToOperand(def->output());
}

#ifdef JS_PUNBOX64
Operand
CodeGeneratorPPC64LE::ToOperandOrRegister64(const LInt64Allocation input)
{
    return ToOperand(input.value());
}
#else
Register64
CodeGeneratorPPC64LE::ToOperandOrRegister64(const LInt64Allocation input)
{
    return ToRegister64(input);
}
#endif

void
CodeGeneratorPPC64LE::branchToBlock(Assembler::FloatFormat fmt, FloatRegister lhs, FloatRegister rhs,
                                       MBasicBlock* mir, Assembler::DoubleCondition cond)
{
    // Skip past trivial blocks.
    Label* label = skipTrivialBlocks(mir)->lir()->label();
    if (fmt == Assembler::DoubleFloat)
        masm.branchDouble(cond, lhs, rhs, label);
    else
        masm.branchFloat(cond, lhs, rhs, label);
}

FrameSizeClass
FrameSizeClass::FromDepth(uint32_t frameDepth)
{
    return FrameSizeClass::None();
}

FrameSizeClass
FrameSizeClass::ClassLimit()
{
    return FrameSizeClass(0);
}

uint32_t
FrameSizeClass::frameSize() const
{
    MOZ_CRASH("PPC64LE does not use frame size classes");
}

void
OutOfLineBailout::accept(CodeGeneratorPPC64LE* codegen)
{
    codegen->visitOutOfLineBailout(this);
}

void
CodeGenerator::visitTestIAndBranch(LTestIAndBranch* test)
{
    ADBlock();
    const LAllocation* opd = test->getOperand(0);
    MBasicBlock* ifTrue = test->ifTrue();
    MBasicBlock* ifFalse = test->ifFalse();

    emitBranch(ToRegister(opd), Imm32(0), Assembler::NonZero, ifTrue, ifFalse);
}

void
CodeGenerator::visitCompare(LCompare* comp)
{
    ADBlock();
    MCompare* mir = comp->mir();
    Assembler::Condition cond = JSOpToCondition(mir->compareType(), comp->jsop());
    const LAllocation* left = comp->getOperand(0);
    const LAllocation* right = comp->getOperand(1);
    const LDefinition* def = comp->getDef(0);

    // 64-bit comparisons.
    if (mir->compareType() == MCompare::Compare_Object ||
        mir->compareType() == MCompare::Compare_Symbol)
    {
        if (right->isGeneralReg())
            masm.cmpPtrSet(cond, ToRegister(left), ToRegister(right), ToRegister(def));
        else
            masm.cmpPtrSet(cond, ToRegister(left), ToAddress(right), ToRegister(def));
        return;
    }

    if (right->isConstant())
        masm.cmp32Set(cond, ToRegister(left), Imm32(ToInt32(right)), ToRegister(def));
    else if (right->isGeneralReg())
        masm.cmp32Set(cond, ToRegister(left), ToRegister(right), ToRegister(def));
    else
        masm.cmp32Set(cond, ToRegister(left), ToAddress(right), ToRegister(def));
}

void
CodeGenerator::visitCompareAndBranch(LCompareAndBranch* comp)
{
    ADBlock();
    MCompare* mir = comp->cmpMir();
    Assembler::Condition cond = JSOpToCondition(mir->compareType(), comp->jsop());

    if (mir->compareType() == MCompare::Compare_Object ||
        mir->compareType() == MCompare::Compare_Symbol) {
        if (comp->right()->isGeneralReg()) {
            emitBranch(ToRegister(comp->left()), ToRegister(comp->right()), cond,
                       comp->ifTrue(), comp->ifFalse());
        } else {
            masm.loadPtr(ToAddress(comp->right()), ScratchRegister);
            emitBranch(ToRegister(comp->left()), ScratchRegister, cond,
                       comp->ifTrue(), comp->ifFalse());
        }
        return;
    }

    if (comp->right()->isConstant()) {
        emitBranch(ToRegister(comp->left()), Imm32(ToInt32(comp->right())), cond,
                   comp->ifTrue(), comp->ifFalse());
    } else if (comp->right()->isGeneralReg()) {
        emitBranch(ToRegister(comp->left()), ToRegister(comp->right()), cond,
                   comp->ifTrue(), comp->ifFalse());
    } else {
        masm.load32(ToAddress(comp->right()), ScratchRegister);
        emitBranch(ToRegister(comp->left()), ScratchRegister, cond,
                   comp->ifTrue(), comp->ifFalse());
    }
}

bool
CodeGeneratorPPC64LE::generateOutOfLineCode()
{
    ADBlock();
    if (!CodeGeneratorShared::generateOutOfLineCode())
        return false;

    if (deoptLabel_.used()) {
        // All non-table-based bailouts will go here.
        masm.bind(&deoptLabel_);

        // Push the frame size, so the handler can recover the IonScript.
        // Frame size is stored in LR and pushed by GenerateBailoutThunk.
        // We have to use LR because generateBailoutTable will implicitly do
        // the same.
        masm.ma_li(ScratchReg, frameSize());
        masm.xs_mtlr(ScratchReg);

        TrampolinePtr handler = gen->jitRuntime()->getGenericBailoutHandler();
        masm.jump(handler);
    }

    return !masm.oom();
}

void
CodeGeneratorPPC64LE::bailoutFrom(Label* label, LSnapshot* snapshot)
{
    ADBlock();
    if (masm.bailed())
        return;

    MOZ_ASSERT_IF(!masm.oom(), label->used());
    MOZ_ASSERT_IF(!masm.oom(), !label->bound());

    encode(snapshot);

    // Though the assembler doesn't track all frame pushes, at least make sure
    // the known value makes sense. We can't use bailout tables if the stack
    // isn't properly aligned to the static frame size.
    MOZ_ASSERT_IF(frameClass_ != FrameSizeClass::None(),
                  frameClass_.frameSize() == masm.framePushed());

    // We don't use table bailouts because retargeting is easier this way.
    InlineScriptTree* tree = snapshot->mir()->block()->trackedTree();
    OutOfLineBailout* ool = new(alloc()) OutOfLineBailout(snapshot, masm.framePushed());
    addOutOfLineCode(ool, new(alloc()) BytecodeSite(tree, tree->script()->code()));

    masm.retarget(label, ool->entry());
}

void
CodeGeneratorPPC64LE::bailout(LSnapshot* snapshot)
{
    Label label;
    masm.jump(&label);
    bailoutFrom(&label, snapshot);
}

void
CodeGenerator::visitMinMaxD(LMinMaxD* ins)
{
    ADBlock();
    FloatRegister first = ToFloatRegister(ins->first());
    FloatRegister second = ToFloatRegister(ins->second());

    MOZ_ASSERT(first == ToFloatRegister(ins->output()));

    if (ins->mir()->isMax())
        masm.maxDouble(second, first, true);
    else
        masm.minDouble(second, first, true);
}

void
CodeGenerator::visitMinMaxF(LMinMaxF* ins)
{
    ADBlock();
    FloatRegister first = ToFloatRegister(ins->first());
    FloatRegister second = ToFloatRegister(ins->second());

    MOZ_ASSERT(first == ToFloatRegister(ins->output()));

    if (ins->mir()->isMax())
        masm.maxFloat32(second, first, true);
    else
        masm.minFloat32(second, first, true);
}

void
CodeGenerator::visitAbsD(LAbsD* ins)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    MOZ_ASSERT(input == ToFloatRegister(ins->output()));
    masm.as_fabs(input, input);
}

void
CodeGenerator::visitAbsF(LAbsF* ins) // dupe
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    MOZ_ASSERT(input == ToFloatRegister(ins->output()));
    masm.as_fabs(input, input);
}

void
CodeGenerator::visitSqrtD(LSqrtD* ins)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    FloatRegister output = ToFloatRegister(ins->output());
    masm.as_fsqrt(output, input);
}

void
CodeGenerator::visitSqrtF(LSqrtF* ins)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    FloatRegister output = ToFloatRegister(ins->output());
    masm.as_fsqrts(output, input);
}

void
CodeGenerator::visitAddI(LAddI* ins)
{
    ADBlock();
    const LAllocation* lhs = ins->getOperand(0);
    const LAllocation* rhs = ins->getOperand(1);
    const LDefinition* dest = ins->getDef(0);

    MOZ_ASSERT(rhs->isConstant() || rhs->isGeneralReg());

    // If there is no snapshot, we don't need to check for overflow.
    if (!ins->snapshot()) {
        if (rhs->isConstant())
            masm.ma_addi(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)));
        else
            masm.as_add(ToRegister(dest), ToRegister(lhs), ToRegister(rhs));
        return;
    }

    Label overflow;
    if (rhs->isConstant())
        masm.ma_addTestOverflow(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)), &overflow);
    else
        masm.ma_addTestOverflow(ToRegister(dest), ToRegister(lhs), ToRegister(rhs), &overflow);

    bailoutFrom(&overflow, ins->snapshot());
}

void
CodeGenerator::visitAddI64(LAddI64* lir)
{
    ADBlock();
    const LInt64Allocation lhs = lir->getInt64Operand(LAddI64::Lhs);
    const LInt64Allocation rhs = lir->getInt64Operand(LAddI64::Rhs);

    MOZ_ASSERT(ToOutRegister64(lir) == ToRegister64(lhs));

    if (IsConstant(rhs)) {
        masm.add64(Imm64(ToInt64(rhs)), ToRegister64(lhs));
        return;
    }

    masm.add64(ToOperandOrRegister64(rhs), ToRegister64(lhs));
}

void
CodeGenerator::visitSubI(LSubI* ins)
{
    ADBlock();
    const LAllocation* lhs = ins->getOperand(0);
    const LAllocation* rhs = ins->getOperand(1);
    const LDefinition* dest = ins->getDef(0);

    MOZ_ASSERT(rhs->isConstant() || rhs->isGeneralReg());

    // If there is no snapshot, we don't need to check for overflow.
    if (!ins->snapshot()) {
        if (rhs->isConstant())
            masm.ma_subi(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)));
        else
            masm.as_subf(ToRegister(dest), ToRegister(rhs), ToRegister(lhs)); // T = B - A
        return;
    }

    Label overflow;
    if (rhs->isConstant())
        masm.ma_subTestOverflow(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)), &overflow);
    else
        masm.ma_subTestOverflow(ToRegister(dest), ToRegister(lhs), ToRegister(rhs), &overflow);

    bailoutFrom(&overflow, ins->snapshot());
}

void
CodeGenerator::visitSubI64(LSubI64* lir)
{
    ADBlock();
    const LInt64Allocation lhs = lir->getInt64Operand(LSubI64::Lhs);
    const LInt64Allocation rhs = lir->getInt64Operand(LSubI64::Rhs);

    MOZ_ASSERT(ToOutRegister64(lir) == ToRegister64(lhs));

    if (IsConstant(rhs)) {
        masm.sub64(Imm64(ToInt64(rhs)), ToRegister64(lhs));
        return;
    }

    masm.sub64(ToOperandOrRegister64(rhs), ToRegister64(lhs));
}

void
CodeGenerator::visitMulI(LMulI* ins)
{
    ADBlock();
    const LAllocation* lhs = ins->lhs();
    const LAllocation* rhs = ins->rhs();
    Register dest = ToRegister(ins->output());
    MMul* mul = ins->mir();

    MOZ_ASSERT_IF(mul->mode() == MMul::Integer, !mul->canBeNegativeZero() && !mul->canOverflow());

    if (rhs->isConstant()) {
        int32_t constant = ToInt32(rhs);
        Register src = ToRegister(lhs);

        // Bailout on -0.0
        if (mul->canBeNegativeZero() && constant <= 0) {
            Assembler::Condition cond = (constant == 0) ? Assembler::LessThan : Assembler::Equal;
            bailoutCmp32(cond, src, Imm32(0), ins->snapshot());
        }

        switch (constant) {
          case -1:
            if (mul->canOverflow())
                bailoutCmp32(Assembler::Equal, src, Imm32(INT32_MIN), ins->snapshot());

            masm.as_neg(dest, src);
            break;
          case 0:
            masm.move32(Imm32(0), dest);
            break;
          case 1:
            masm.move32(src, dest);
            break;
          case 2:
            if (mul->canOverflow()) {
                Label mulTwoOverflow;
                masm.ma_addTestOverflow(dest, src, src, &mulTwoOverflow);

                bailoutFrom(&mulTwoOverflow, ins->snapshot());
            } else {
                masm.as_add(dest, src, src);
            }
            break;
          default:
            uint32_t shift = FloorLog2(constant);

            if (!mul->canOverflow() && (constant > 0)) {
                // If it cannot overflow, we can do lots of optimizations.
                uint32_t rest = constant - (1 << shift);

                // See if the constant has one bit set, meaning it can be
                // encoded as a bitshift.
                if ((1 << shift) == constant) {
                    MOZ_ASSERT(shift < 32);
                    masm.xs_slwi(dest, src, shift);
                    return;
                }

                // If the constant cannot be encoded as (1<<C1), see if it can
                // be encoded as (1<<C1) | (1<<C2), which can be computed
                // using an add and a shift.
                uint32_t shift_rest = FloorLog2(rest);
                if (src != dest && (1u << shift_rest) == rest) {
                    masm.xs_slwi(dest, src, shift - shift_rest);
                    masm.as_add(dest, dest, src);
                    if (shift_rest != 0)
                        masm.xs_slwi(dest, dest, shift_rest);
                    return;
                }
            }

            if (mul->canOverflow() && (constant > 0) && (src != dest)) {
                // To stay on the safe side, only optimize things that are a
                // power of 2.

                if ((1 << shift) == constant) {
                    // dest = lhs * pow(2, shift)
                    MOZ_ASSERT(shift < 32);
                    masm.xs_slwi(dest, src, shift);
                    // At runtime, check (lhs == dest >> shift). If this does
                    // not hold, some bits were lost due to overflow, and the
                    // computation should be resumed as a double.
                    masm.as_srawi(ScratchRegister, dest, shift);
                    bailoutCmp32(Assembler::NotEqual, src, ScratchRegister, ins->snapshot());
                    return;
                }
            }

            if (mul->canOverflow()) {
                Label mulConstOverflow;
                masm.ma_mul_branch_overflow(dest, ToRegister(lhs), Imm32(ToInt32(rhs)),
                                            &mulConstOverflow);

                bailoutFrom(&mulConstOverflow, ins->snapshot());
            } else {
                masm.ma_mul(dest, src, Imm32(ToInt32(rhs)));
            }
            break;
        }
    } else {
        Label multRegOverflow;

        if (mul->canOverflow()) {
            masm.ma_mul_branch_overflow(dest, ToRegister(lhs), ToRegister(rhs), &multRegOverflow);
            bailoutFrom(&multRegOverflow, ins->snapshot());
        } else {
            masm.as_mullw(dest, ToRegister(lhs), ToRegister(rhs));
        }

        if (mul->canBeNegativeZero()) {
            Label done;
            masm.ma_b(dest, dest, &done, Assembler::NonZero, ShortJump);

            // Result is -0 if lhs or rhs is negative.
            // In that case result must be double value so bailout
            Register scratch = SecondScratchReg;
            masm.as_or(scratch, ToRegister(lhs), ToRegister(rhs));
            bailoutCmp32(Assembler::Signed, scratch, scratch, ins->snapshot());

            masm.bind(&done);
        }
    }
}

void
CodeGenerator::visitMulI64(LMulI64* lir)
{
    ADBlock();
    const LInt64Allocation lhs = lir->getInt64Operand(LMulI64::Lhs);
    const LInt64Allocation rhs = lir->getInt64Operand(LMulI64::Rhs);
    const Register64 output = ToOutRegister64(lir);

    if (IsConstant(rhs)) {
        int64_t constant = ToInt64(rhs);
        switch (constant) {
          case -1:
            masm.neg64(ToRegister64(lhs));
            return;
          case 0:
            masm.xor64(ToRegister64(lhs), ToRegister64(lhs));
            return;
          case 1:
            // nop
            return;
          default:
            if (constant > 0) {
                if (mozilla::IsPowerOfTwo(static_cast<uint32_t>(constant + 1))) {
                    masm.move64(ToRegister64(lhs), output);
                    masm.lshift64(Imm32(FloorLog2(constant + 1)), output);
                    masm.sub64(ToRegister64(lhs), output);
                    return;
                } else if (mozilla::IsPowerOfTwo(static_cast<uint32_t>(constant - 1))) {
                    masm.move64(ToRegister64(lhs), output);
                    masm.lshift64(Imm32(FloorLog2(constant - 1u)), output);
                    masm.add64(ToRegister64(lhs), output);
                    return;
                }
                // Use shift if constant is power of 2.
                int32_t shift = mozilla::FloorLog2(constant);
                if (int64_t(1) << shift == constant) {
                    masm.lshift64(Imm32(shift), ToRegister64(lhs));
                    return;
                }
            }
            Register temp = ToTempRegisterOrInvalid(lir->temp());
            masm.mul64(Imm64(constant), ToRegister64(lhs), temp);
        }
    } else {
        Register temp = ToTempRegisterOrInvalid(lir->temp());
        masm.mul64(ToOperandOrRegister64(rhs), ToRegister64(lhs), temp);
    }
}

void
CodeGenerator::visitDivI(LDivI* ins)
{
    ADBlock();
    // divwo will automatically set the Overflow bit if INT32_MIN/-1 is
    // performed, or if we divide by zero, so we just bailout based on that.
    // However, it does not trigger an exception for a negative zero result,
    // so we must check that first.

    // Extract the registers from this instruction.
    Register lhs = ToRegister(ins->lhs());
    Register rhs = ToRegister(ins->rhs());
    Register dest = ToRegister(ins->output());
    Register temp = ToRegister(ins->getTemp(0));
    MDiv* mir = ins->mir();

    Label done;

    // Handle negative 0. (0/-Y)
    if (!mir->canTruncateNegativeZero() && mir->canBeNegativeZero()) {
        Label nonzero;
        masm.ma_b(lhs, lhs, &nonzero, Assembler::NonZero, ShortJump);
        bailoutCmp32(Assembler::LessThan, rhs, Imm32(0), ins->snapshot());
        masm.bind(&nonzero);
    }

    // Not negative zero. So: DIVIDE! AND! CONQUER!
    if (ins->snapshot()) {
        // If Overflow is set, we must bail out. But only do this if
        // there is a snapshot, because if there isn't, Ion already knows
        // this operation is infallible (and we can avoid checking
        // for overflow, which is slightly faster).
        masm.xs_li(output, 0);
        masm.xs_mtxer(output); // whack XER[SO]
        masm.as_divwo_rc(output, lhs, rhs); // T = A / B

        // Did we trap?
        masm.ma_bc(Assembler::NoSO, &noOverflow, ShortJump);
        // Yes. Determine how.
        MOZ_ASSERT(mir->canBeNegativeOverflow() || mir->canBeDivideByZero());
        if (mir->canBeNegativeOverflow()) {
            Label notNegOne;

            if (mir->canBeDivideByZero()) {
                // If rhs is -1, then we overflowed by dividing INT32_MIN;
                // otherwise, it must be divide by zero.
                masm.branchPtr(Assembler::NotEqual, rhs, ImmWord(-1), &notNegOne);
            }

            if (mir->trapOnError()) {
                masm.wasmTrap(wasm::Trap::IntegerOverflow, mir->bytecodeOffset());
            } else if (mir->canTruncateOverflow()) {
                // (-INT32_MIN)|0 == INT32_MIN
                masm.move32(Imm32(INT32_MIN), dest);
                masm.ma_b(&done, ShortJump);
            } else {
                MOZ_ASSERT(mir->fallible());
                bailout(ins->snapshot());
            }

            masm.bind(&notNegOne);
        }
        if (mir->canBeDivideByZero()) {
            // Must have been divide by zero.
            // If we can truncate division, then a truncated division by
            // zero is always zero, and not actually an exception.
            if (mir->trapOnError()) {
                masm.wasmTrap(wasm::Trap::IntegerDivideByZero, mir->bytecodeOffset());
            } else if (mir->canTruncateInfinities()) {
                masm.move32(Imm32(0), dest);
                masm.ma_b(&done, ShortJump);
            } else {
                MOZ_ASSERT(mir->fallible());
                bailout(ins->snapshot());
            }
        }
    } else {
        masm.as_divw(output, lhs, rhs);
    }

    masm.bind(&noOverflow);

    if (!mir->canTruncateRemainder()) {
        MOZ_ASSERT(mir->fallible());

        // Recover the remainder to see if we need to bailout.
        // We don't need to check overflow; we know it can't.
        masm.as_mullw(ScratchRegister, output, rhs);
        masm.as_subf(SecondScratchReg, ScratchRegister, lhs); // T = B - A
        bailoutCmp32(Assembler::NotEqual, SecondScratchReg, Imm32(0), ins->snapshot());
    }

    masm.bind(&done);
}

void
CodeGenerator::visitDivPowTwoI(LDivPowTwoI* ins)
{
    ADBlock();
    Register lhs = ToRegister(ins->numerator());
    Register dest = ToRegister(ins->output());
    Register tmp = ToRegister(ins->getTemp(0));
    int32_t shift = ins->shift();

    if (shift != 0) {
        MOZ_ASSERT(shift < 32);
        MDiv* mir = ins->mir();
        if (!mir->isTruncated()) {
            // If the remainder is going to be != 0, bailout since this must
            // be a double.
            masm.xs_slwi(tmp, lhs, 32 - shift);
            bailoutCmp32(Assembler::NonZero, tmp, tmp, ins->snapshot());
        }

        if (!mir->canBeNegativeDividend()) {
            // Numerator is unsigned, so needs no adjusting. Do the shift.
            masm.as_srawi(dest, lhs, shift);
            return;
        }

        // Adjust the value so that shifting produces a correctly rounded result
        // when the numerator is negative. See 10-1 "Signed Division by a Known
        // Power of 2" in Henry S. Warren, Jr.'s Hacker's Delight.
        if (shift > 1) {
            masm.as_srawi(tmp, lhs, 31);
            masm.xs_srwi(tmp, tmp, 32 - shift);
            masm.add32(lhs, tmp);
        } else {
            MOZ_ASSERT(shift == 1);
            masm.xs_srwi(tmp, lhs, 31);
            masm.add32(lhs, tmp);
        }

        // Do the shift.
        masm.as_srawi(dest, tmp, shift);
    } else {
        if (lhs != dest)        
            masm.move32(lhs, dest);
    }
}

void
CodeGenerator::visitModI(LModI* ins)
{
    ADBlock();

    // Extract the registers from this instruction
    Register lhs = ToRegister(ins->lhs());
    Register rhs = ToRegister(ins->rhs());
    Register dest = ToRegister(ins->output());
    Register callTemp = ToRegister(ins->callTemp());
    MMod* mir = ins->mir();
    Label done, prevent;

    masm.move32(lhs, callTemp);

    // If computing 0/x where x < 0, divwo won't raise an exception but
    // we have to return -0.0 (which requires a bailout). Since we have to
    // probe the y/0 case necessarily, let's just check for all of them.
    if (mir->canBeDivideByZero()) {
        if (mir->isTruncated()) {
            if (mir->trapOnError()) {
                Label nonZero;
                masm.ma_b(rhs, rhs, &nonZero, Assembler::NonZero, ShortJump);
                masm.wasmTrap(wasm::Trap::IntegerDivideByZero, mir->bytecodeOffset());
                masm.bind(&nonZero);
            } else {
                Label skip;
                masm.ma_b(rhs, Imm32(0), &skip, Assembler::NotEqual, ShortJump);
                masm.move32(Imm32(0), dest);
                masm.ma_b(&done, ShortJump);
                masm.bind(&skip);
            }
        } else {
            MOZ_ASSERT(mir->fallible());
            bailoutCmp32(Assembler::Equal, rhs, Imm32(0), ins->snapshot());
        }
    }

    if (mir->canBeNegativeDividend()) {
        Label notNegative;
        masm.ma_b(rhs, Imm32(0), &notNegative, Assembler::GreaterThan, ShortJump);
        if (mir->isTruncated()) {
            // NaN|0 == 0 and (0 % -X)|0 == 0
            Label skip;
            masm.ma_b(lhs, Imm32(0), &skip, Assembler::NotEqual, ShortJump);
            masm.move32(Imm32(0), dest);
            masm.ma_b(&done, ShortJump);
            masm.bind(&skip);
        } else {
            MOZ_ASSERT(mir->fallible());
            bailoutCmp32(Assembler::Equal, lhs, Imm32(0), ins->snapshot());
        }
        masm.bind(&notNegative);
    }

    // Do the division. Since the divide-by-zero case is covered, if divwo
    // flags overflow, then it must be INT_MIN % -1.
    if (mir->canBeNegativeDividend()) {
        Label noOverflow;

        masm.xs_li(dest, 0);
        masm.xs_mtxer(dest); // whack XER[SO]
        masm.as_divwo_rc(dest, lhs, rhs);
        masm.ma_bc(Assembler::NoSO, &noOverflow, ShortJump);

        // Overflowed.
        if (mir->isTruncated()) {
            // (INT_MIN % -1)|0 == 0
            Label skip;
            masm.ma_b(rhs, Imm32(-1), &skip, Assembler::NotEqual, ShortJump);
            masm.move32(Imm32(0), dest);
            masm.ma_b(&done, ShortJump);
            masm.bind(&skip);
        } else {
            MOZ_ASSERT(mir->fallible());
            bailoutCmp32(Assembler::Equal, rhs, Imm32(-1), ins->snapshot());
        }
        masm.bind(&noOverflow);
    } else {
        // We already checked for divide by zero, so no need to
        // expend cycles checking for overflow even if a snapshot
        // is present because the other case cannot happen.
        masm.as_divw(dest, lhs, rhs);
    }

    // If X%Y == 0 and X < 0, then we *actually* wanted to return -0.0
    if (mir->canBeNegativeDividend()) {
        if (mir->isTruncated()) {
            // -0.0|0 == 0
        } else {
            MOZ_ASSERT(mir->fallible());
            // See if X < 0
            masm.ma_b(dest, Imm32(0), &done, Assembler::NotEqual, ShortJump);
            bailoutCmp32(Assembler::Signed, callTemp, Imm32(0), ins->snapshot());
        }
    }
    masm.bind(&done);
}

void
CodeGenerator::visitModPowTwoI(LModPowTwoI* ins)
{
    ADBlock();

    Register in = ToRegister(ins->getOperand(0));
    Register out = ToRegister(ins->getDef(0));
    MMod* mir = ins->mir();
    Label negative, done;

    masm.move32(in, out);
    masm.ma_b(in, in, &done, Assembler::Zero, ShortJump);
    // Switch based on sign of the lhs.
    // Positive numbers are just a bitmask
    masm.ma_b(in, in, &negative, Assembler::Signed, ShortJump);
    {
        masm.and32(Imm32((1 << ins->shift()) - 1), out);
        masm.ma_b(&done, ShortJump);
    }

    // Negative numbers need a negate, bitmask, negate
    {
        masm.bind(&negative);
        masm.neg32(out);
        masm.and32(Imm32((1 << ins->shift()) - 1), out);
        masm.neg32(out);
    }
    if (mir->canBeNegativeDividend()) {
        if (!mir->isTruncated()) {
            MOZ_ASSERT(mir->fallible());
            bailoutCmp32(Assembler::Equal, out, zero, ins->snapshot());
        } else {
            // -0|0 == 0
        }
    }
    masm.bind(&done);
}

void
CodeGenerator::visitModMaskI(LModMaskI* ins)
{
    ADBlock();

    Register src = ToRegister(ins->getOperand(0));
    Register dest = ToRegister(ins->getDef(0));
    Register tmp0 = ToRegister(ins->getTemp(0));
    Register tmp1 = ToRegister(ins->getTemp(1));
    MMod* mir = ins->mir();

    if (!mir->isTruncated() && mir->canBeNegativeDividend()) {
        MOZ_ASSERT(mir->fallible());

        Label bail;
        masm.ma_mod_mask(src, dest, tmp0, tmp1, ins->shift(), &bail);
        bailoutFrom(&bail, ins->snapshot());
    } else {
        masm.ma_mod_mask(src, dest, tmp0, tmp1, ins->shift(), nullptr);
    }
}

void
CodeGenerator::visitBitNotI(LBitNotI* ins)
{
    ADBlock();

    const LAllocation* input = ins->getOperand(0);
    const LDefinition* dest = ins->getDef(0);
    MOZ_ASSERT(!input->isConstant());

    masm.ma_not(ToRegister(dest), ToRegister(input));
}

void
CodeGenerator::visitBitOpI(LBitOpI* ins)
{
    ADBlock();

    const LAllocation* lhs = ins->getOperand(0);
    const LAllocation* rhs = ins->getOperand(1);
    const LDefinition* dest = ins->getDef(0);
    // all of these bitops should be either imm32's, or integer registers.
    switch (ins->bitop()) {
      case JSOP_BITOR:
        if (rhs->isConstant())
            masm.ma_or(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)));
        else
            masm.as_or(ToRegister(dest), ToRegister(lhs), ToRegister(rhs));
        break;
      case JSOP_BITXOR:
        if (rhs->isConstant())
            masm.ma_xor(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)));
        else
            masm.as_xor(ToRegister(dest), ToRegister(lhs), ToRegister(rhs));
        break;
      case JSOP_BITAND:
        if (rhs->isConstant())
            masm.ma_and(ToRegister(dest), ToRegister(lhs), Imm32(ToInt32(rhs)));
        else
            masm.as_and(ToRegister(dest), ToRegister(lhs), ToRegister(rhs));
        break;
      default:
        MOZ_CRASH("unexpected binary opcode");
    }
}

void
CodeGenerator::visitBitOpI64(LBitOpI64* lir)
{
    ADBlock();
    const LInt64Allocation lhs = lir->getInt64Operand(LBitOpI64::Lhs);
    const LInt64Allocation rhs = lir->getInt64Operand(LBitOpI64::Rhs);

    MOZ_ASSERT(ToOutRegister64(lir) == ToRegister64(lhs));

    switch (lir->bitop()) {
      case JSOP_BITOR:
        if (IsConstant(rhs))
            masm.or64(Imm64(ToInt64(rhs)), ToRegister64(lhs));
        else
            masm.or64(ToOperandOrRegister64(rhs), ToRegister64(lhs));
        break;
      case JSOP_BITXOR:
        if (IsConstant(rhs))
            masm.xor64(Imm64(ToInt64(rhs)), ToRegister64(lhs));
        else
            masm.xor64(ToOperandOrRegister64(rhs), ToRegister64(lhs));
        break;
      case JSOP_BITAND:
        if (IsConstant(rhs))
            masm.and64(Imm64(ToInt64(rhs)), ToRegister64(lhs));
        else
            masm.and64(ToOperandOrRegister64(rhs), ToRegister64(lhs));
        break;
      default:
        MOZ_CRASH("unexpected binary opcode");
    }
}

void
CodeGenerator::visitShiftI(LShiftI* ins)
{
    ADBlock();
    Register lhs = ToRegister(ins->lhs());
    const LAllocation* rhs = ins->rhs();
    Register dest = ToRegister(ins->output());

    if (rhs->isConstant()) {
        int32_t shift = ToInt32(rhs) & 0x1F;
        MOZ_ASSERT(shift > 0);
        switch (ins->bitop()) {
          case JSOP_LSH:
            if (shift)
                masm.xs_slwi(dest, lhs, shift);
            else
                masm.move32(lhs, dest);
            break;
          case JSOP_RSH:
            if (shift)
                masm.as_srawi(dest, lhs, shift);
            else
                masm.move32(lhs, dest);
            break;
          case JSOP_URSH:
            if (shift) {
                masm.xs_srwi(dest, lhs, shift);
            } else {
                // x >>> 0 can overflow.
                if (ins->mir()->toUrsh()->fallible())
                    bailoutCmp32(Assembler::LessThan, lhs, Imm32(0), ins->snapshot());
                masm.move32(lhs, dest);
            }
            break;
          default:
            MOZ_CRASH("Unexpected shift op");
        }
    } else {
        // The shift amounts should be AND'ed into the 0-31 range.
        masm.as_andi_rc(dest, ToRegister(rhs), 0x1f);

        switch (ins->bitop()) {
          case JSOP_LSH:
            masm.as_slw(dest, lhs, dest);
            break;
          case JSOP_RSH:
            masm.as_sraw(dest, lhs, dest);
            break;
          case JSOP_URSH:
            masm.as_srw(dest, lhs, dest);
            if (ins->mir()->toUrsh()->fallible()) {
                // x >>> 0 can overflow.
                bailoutCmp32(Assembler::LessThan, dest, Imm32(0), ins->snapshot());
            }
            break;
          default:
            MOZ_CRASH("Unexpected shift op");
        }
    }
}

void
CodeGenerator::visitShiftI64(LShiftI64* lir)
{
    ADBlock();
    const LInt64Allocation lhs = lir->getInt64Operand(LShiftI64::Lhs);
    LAllocation* rhs = lir->getOperand(LShiftI64::Rhs);

    MOZ_ASSERT(ToOutRegister64(lir) == ToRegister64(lhs));

    if (rhs->isConstant()) {
        int32_t shift = int32_t(rhs->toConstant()->toInt64() & 0x3F);
        switch (lir->bitop()) {
          case JSOP_LSH:
            if (shift)
                masm.lshift64(Imm32(shift), ToRegister64(lhs));
            break;
          case JSOP_RSH:
            if (shift)
                masm.rshift64Arithmetic(Imm32(shift), ToRegister64(lhs));
            break;
          case JSOP_URSH:
            if (shift)
                masm.rshift64(Imm32(shift), ToRegister64(lhs));
            break;
          default:
            MOZ_CRASH("Unexpected shift op");
        }
        return;
    }

    switch (lir->bitop()) {
      case JSOP_LSH:
        masm.lshift64(ToRegister(rhs), ToRegister64(lhs));
        break;
      case JSOP_RSH:
        masm.rshift64Arithmetic(ToRegister(rhs), ToRegister64(lhs));
        break;
      case JSOP_URSH:
        masm.rshift64(ToRegister(rhs), ToRegister64(lhs));
        break;
      default:
        MOZ_CRASH("Unexpected shift op");
    }
}

void
CodeGenerator::visitRotateI64(LRotateI64* lir)
{
    ADBlock();
    MRotate* mir = lir->mir();
    LAllocation* count = lir->count();

    Register64 input = ToRegister64(lir->input());
    Register64 output = ToOutRegister64(lir);
    Register temp = ToTempRegisterOrInvalid(lir->temp());

    MOZ_ASSERT(input == output);

    if (count->isConstant()) {
        int32_t c = int32_t(count->toConstant()->toInt64() & 0x3F);
        if (!c) {
            masm.move64(input, output);
            return;
        }
        if (mir->isLeftRotate())
            masm.rotateLeft64(Imm32(c), input, output, temp);
        else
            masm.rotateRight64(Imm32(c), input, output, temp);
    } else {
        if (mir->isLeftRotate())
            masm.rotateLeft64(ToRegister(count), input, output, temp);
        else
            masm.rotateRight64(ToRegister(count), input, output, temp);
    }
}

void
CodeGenerator::visitUrshD(LUrshD* ins)
{
    ADBlock();
    Register lhs = ToRegister(ins->lhs());
    Register temp = ToRegister(ins->temp());

    const LAllocation* rhs = ins->rhs();
    FloatRegister out = ToFloatRegister(ins->output());

    if (rhs->isConstant()) {
        masm.ma_srl(temp, lhs, Imm32(ToInt32(rhs)));
    } else {
        masm.as_srw(temp, lhs, ToRegister(rhs));
    }

    masm.convertUInt32ToDouble(temp, out);
}

void
CodeGenerator::visitClzI(LClzI* ins)
{
    ADBlock();
    Register input = ToRegister(ins->input());
    Register output = ToRegister(ins->output());

    masm.as_cntlzw(output, input);
}

void
CodeGenerator::visitCtzI(LCtzI* ins)
{
    ADBlock();
    Register input = ToRegister(ins->input());
    Register output = ToRegister(ins->output());

    masm.as_cnttzw(output, input);
}

void
CodeGenerator::visitPopcntI(LPopcntI* ins)
{
    ADBlock();
    Register input = ToRegister(ins->input());
    Register output = ToRegister(ins->output());

    masm.as_popcntw(output, input);
}

void
CodeGenerator::visitPopcntI64(LPopcntI64* ins)
{
    ADBlock();
    Register64 input = ToRegister64(ins->getInt64Operand(0));
    Register64 output = ToOutRegister64(ins);

    masm.as_popcntd(output, input);
}

void
CodeGenerator::visitPowHalfD(LPowHalfD* ins)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    FloatRegister output = ToFloatRegister(ins->output());

    Label done, skip;

    // Masm.pow(-Infinity, 0.5) == Infinity.
    masm.loadConstantDouble(NegativeInfinity<double>(), ScratchDoubleReg);
    masm.ma_bc1d(input, ScratchDoubleReg, &skip, Assembler::DoubleNotEqualOrUnordered, ShortJump);
    masm.as_fneg(output, ScratchDoubleReg);
    masm.ma_b(&done, ShortJump);

    masm.bind(&skip);
    // Math.pow(-0, 0.5) == 0 == Math.pow(0, 0.5).
    // Adding 0 converts any -0 to 0.
    masm.loadConstantDouble(0.0, ScratchDoubleReg);
    masm.as_fadd(output, input, ScratchDoubleReg);
    masm.as_fsqrt(output, output);

    masm.bind(&done);
}

MoveOperand
CodeGeneratorPPC64LE::toMoveOperand(LAllocation a) const
{
    if (a.isGeneralReg())
        return MoveOperand(ToRegister(a));
    if (a.isFloatReg()) {
        return MoveOperand(ToFloatRegister(a));
    }
    int32_t offset = ToStackOffset(a);
    MOZ_ASSERT((offset & 3) == 0);

    return MoveOperand(StackPointer, offset);
}

void
CodeGenerator::visitMathD(LMathD* math)
{
    ADBlock();
    FloatRegister src1 = ToFloatRegister(math->getOperand(0));
    FloatRegister src2 = ToFloatRegister(math->getOperand(1));
    FloatRegister output = ToFloatRegister(math->getDef(0));

    switch (math->jsop()) {
      case JSOP_ADD:
        masm.as_fadd(output, src1, src2);
        break;
      case JSOP_SUB:
        masm.as_fsub(output, src1, src2); // T = A - B
        break;
      case JSOP_MUL:
        masm.as_fmul(output, src1, src2);
        break;
      case JSOP_DIV:
        masm.as_fdiv(output, src1, src2);
        break;
      default:
        MOZ_CRASH("unexpected opcode");
    }
}

void
CodeGenerator::visitMathF(LMathF* math)
{
    ADBlock();
    FloatRegister src1 = ToFloatRegister(math->getOperand(0));
    FloatRegister src2 = ToFloatRegister(math->getOperand(1));
    FloatRegister output = ToFloatRegister(math->getDef(0));

    switch (math->jsop()) {
      case JSOP_ADD:
        masm.as_fadds(output, src1, src2);
        break;
      case JSOP_SUB:
        masm.as_fsubs(output, src1, src2);
        break;
      case JSOP_MUL:
        masm.as_fmuls(output, src1, src2);
        break;
      case JSOP_DIV:
        masm.as_fdivs(output, src1, src2);
        break;
      default:
        MOZ_CRASH("unexpected opcode");
    }
}

// Common code for visitFloor/F, visitCeil/F and visitRound/F.
// This essentially combines branchTruncateDouble and convertDoubleToInt32.
// The fudge register is considered volatile and may be clobbered if provided.
static void
PPCRounder(MacroAssembler &masm,
           FloatRegister input,
           FloatRegister scratch,
           FloatRegister fudge,
           Register output,
           Label *bailoutBogusFloat,
           Label *bailoutOverflow,
           uint32_t rmode,
           bool ceilCheck,
           bool roundCheck)
{
    FloatRegister victim = input;
    Label done, done2, skipCheck, skipCheck2, skipCheck3;

    // Prepare zero checks for the next step.
    // If fudge is provided, it's ordered, so use a sub to generate zero.
    if (fudge != InvalidFloatReg) {
        masm.as_fsub(scratch, fudge, fudge); // faster
    } else {
        masm.loadConstantFloat32(0.0f, scratch);
    }
    masm.as_fcmpu(input, scratch);
    // We need the result of this comparison one more time at the end if we are round()ing, so
    // put another copy in CR1.
    if (roundCheck)
        masm.as_fcmpu(input, scratch, cr1);

    // Since we have to invariably put the float on the stack at some point, do it
    // here so we can schedule better.
    masm.as_stfdu(input, stackPointerRegister, -8);
    if (ceilCheck) {
        // ceil() has an edge case for -1 < x < 0: it should be -0.
        // We bail out for those values below.
        
        masm.ma_bc(Assembler::GreaterThan, &skipCheck, ShortJump);
        masm.loadConstantFloat32(-1.0f, scratch);
        masm.as_fcmpu(input, scratch);
        masm.ma_bc(Assembler::DoubleLessThanOrEqual, &skipCheck2, ShortJump);
    } else {
        // Check for equality with zero.
        // If ordered and non-zero, proceed to truncation.
        masm_ma_bc(Assembler::DoubleNotEqual, &skipCheck3, ShortJump);
    }
    // We are either zero, NaN or negative zero. Analyse the float's upper word.
    // If it's non-zero, oops.
    // (We also get here if the ceil check tripped, but we'd be bailing out anyway, so.)
    masm.as_lwz(tempRegister, stackPointerRegister, 4); // ENDIAN!!!
    masm.as_cmpi(tempRegister, 0);
    masm.as_addi(stackPointerRegister, stackPointerRegister, 8);
    masm.ma_bc(Assembler::NotEqual, bailoutBogusFloat); // either -0.0 or NaN, or (ceil) non-zero
    // It's zero; return zero.
    masm.ma_li(output, 0);
    masm.ma_b(&done, ShortJump);

    // Now we have a valid, non-zero float.
    masm.bind(&skipCheck);
    masm.bind(&skipCheck2);
    masm.bind(&skipCheck3);
    // If a fudge factor was provided, add it now.
    if (fudge != InvalidFloatReg) {
        masm.as_fadd(fudge, fudge, input);
        victim = fudge;
    }

    masm.as_mtfsb0(23); // whack FPSCR[VXCVI]
    // Set the current rounding mode, if the mode is not 0x01 (because we can just fctiwz).
    // Set it back to 0 when we're done.
    // Don't update the CR; we only want the FPSCR.
    if (rmode != 0x01) {
        if (rmode == 0x03) {
            masm.as_mtfsfi(7,3);
        } else {
            MOZ_ASSERT(rmode == 0x02);
            masm.as_mtfsb1(30);
        }
        // Convert.
        masm.as_fctiw(scratch, victim);
        if (rmode == 0x03) {
            masm.as_mtfsfi(7,0);
        } else {
            MOZ_ASSERT(rmode == 0x02);
            masm.as_mtfsb0(30);
        }
    } else {
        // Rounding mode 1 is truncation. fctiwz sets FPSCR[FI]
        // if the conversion was inexact, and we bailout on that.
        masm.as_mtfsb0(14); // whack FI
        masm.as_fctiwz(scratch, victim);
        masm_as_mcrfs(cr0, 3); // new dispatch group; FI -> cr0::EQ
        masm.ma_bc(Assembler::Equal, bailoutOverflow);
    }
    masm.as_stfd(scratch, StackPointer, 0); // clobber original float on stack
    masm.as_mcrfs(cr0, 5); // new dispatch group; VXCVI -> cr0::SOBit
    // Pull out the lower 32 bits. This is the result.
    masm.as_lwz(output, StackPointer, 0); // ENDIAN!!!
    masm.as_addi(StackPointer, StackPointer, 8);
    masm.ma_bc(Assembler::SO, bailoutOverflow);
		
    // round() must bail out if the result is zero and the input was negative
    // (copied in CR1 from the beginning). By this point, we can assume the
    // result was ordered.
    if (roundCheck) {
        masm.as_cmpi(output, 0); // "free"
        masm.ma_bc(cr1, Assembler::DoubleGreaterThan, &done2, ShortJump);
        masm.ma_bc(Assembler::Equal, bailoutBogusFloat); // need to return -0.0
    }

    masm.bind(&done);
    masm.bind(&done2);
}

// fctiw can (to our displeasure) round down, not up. For example, in rounding
// mode 0x00, -3.5 rounds to -4. Arguably that's right, but JS expects -3. The
// simplest fix for that is to add 0.5 and round towards -Inf, which also
// works in the positive case. However, we can't add it until after the -0/NaN
// checks, so we provide it as a "fudge" register.
void
CodeGenerator::visitRound(LRound *lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;
    FloatRegister input = ToFloatRegister(lir->input());
    FloatRegister temp = ToFloatRegister(lir->temp());
	
    masm.point5Double(temp);
    PPCRounder(masm, input, ScratchDoubleReg, temp, ToRegister(lir->output()),
               &bailoutBogusFloat, &bailoutOverflow,
               /* rounding bits = */ 0x03,
               /* ceilCheck = */     false,
               /* roundCheck = */    true);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}
void
CodeGeneratorPPC::visitRoundF(LRoundF *lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;
    FloatRegister input = ToFloatRegister(lir->input());
    FloatRegister temp = ToFloatRegister(lir->temp());
	
    masm.point5Double(temp);
    PPCRounder(masm, input, ScratchDoubleReg, temp, ToRegister(lir->output()),
               &bailoutBogusFloat, &bailoutOverflow,
               /* rounding bits = */ 0x03,
               /* ceilCheck = */     false,
               /* roundCheck = */    true);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}

void
CodeGeneratorPPC::visitFloor(LFloor *lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;
	
    FPRounder(masm, ToFloatRegister(lir->input()), ScratchDoubleReg, InvalidFloatReg,
              ToRegister(lir->output()), &bailoutBogusFloat, &bailoutOverflow,
              /* rounding bits = */ 0x03,
              /* ceilCheck = */     false,
              /* roundCheck = */    false);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}
void
CodeGeneratorPPC::visitFloorF(LFloorF *lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;
	
    FPRounder(masm, ToFloatRegister(lir->input()), ScratchFloat32Reg, InvalidFloatReg,
              ToRegister(lir->output()), &bailoutBogusFloat, &bailoutOverflow,
              /* rounding bits = */ 0x03,
              /* ceilCheck = */     false,
              /* roundCheck = */    false);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}

void
CodeGeneratorPPC::visitCeil(LCeil *lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;
	
    FPRounder(masm, ToFloatRegister(lir->input()), ScratchDoubleReg, InvalidFloatReg,
              ToRegister(lir->output()), &bailoutBogusFloat, &bailoutOverflow,
              /* rounding bits = */ 0x02,
              /* ceilCheck = */     true,
              /* roundCheck = */    false);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}
void
CodeGeneratorPPC::visitCeilF(LCeilF *lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;
	
    FPRounder(masm, ToFloatRegister(lir->input()), ScratchFloat32Reg, InvalidFloatReg,
              ToRegister(lir->output()), &bailoutBogusFloat, &bailoutOverflow,
              /* rounding bits = */ 0x02,
              /* ceilCheck = */     true,
              /* roundCheck = */    false);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}

void
CodeGenerator::visitTrunc(LTrunc* lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;

    FPRounder(masm, ToFloatRegister(lir->input()), ScratchDoubleReg, InvalidFloatReg,
              ToRegister(lir->output(), &bailoutBogusFloat, &bailoutOverflow,
              /* rounding bits = */ 0x01,
              /* ceilCheck = */     false,
              /* roundCheck = */    false);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}
void
CodeGenerator::visitTruncF(LTruncF* lir)
{
    ADBlock();
    Label bailoutBogusFloat, bailoutOverflow;

    FPRounder(masm, ToFloatRegister(lir->input()), ScratchFloat32Reg, InvalidFloatReg,
              ToRegister(lir->output(), &bailoutBogusFloat, &bailoutOverflow,
              /* rounding bits = */ 0x01,
              /* ceilCheck = */     false,
              /* roundCheck = */    false);
    bailoutFrom(&bailoutBogusFloat, lir->snapshot());
    bailoutFrom(&bailoutOverflow, lir->snapshot());
}

void
CodeGenerator::visitTruncateDToInt32(LTruncateDToInt32* ins)
{
    emitTruncateDouble(ToFloatRegister(ins->input()), ToRegister(ins->output()),
                       ins->mir());
}

void
CodeGenerator::visitTruncateFToInt32(LTruncateFToInt32* ins)
{
    emitTruncateFloat32(ToFloatRegister(ins->input()), ToRegister(ins->output()),
                        ins->mir());
}

void
CodeGenerator::visitWasmTruncateToInt32(LWasmTruncateToInt32* lir)
{
    ADBlock();
    auto input = ToFloatRegister(lir->input());
    auto output = ToRegister(lir->output());

    MWasmTruncateToInt32* mir = lir->mir();
    MIRType fromType = mir->input()->type();

    MOZ_ASSERT(fromType == MIRType::Double || fromType == MIRType::Float32);

    auto* ool = new (alloc()) OutOfLineWasmTruncateCheck(mir, input, output);
    addOutOfLineCode(ool, mir);

    Label* oolEntry = ool->entry();
    if (mir->isUnsigned()) {
        if (fromType == MIRType::Double)
            masm.wasmTruncateDoubleToUInt32(input, output, mir->isSaturating(), oolEntry);
        else if (fromType == MIRType::Float32)
            masm.wasmTruncateFloat32ToUInt32(input, output, mir->isSaturating(), oolEntry);
        else
            MOZ_CRASH("unexpected type");

        masm.bind(ool->rejoin());
        return;
    }

    if (fromType == MIRType::Double)
        masm.wasmTruncateDoubleToInt32(input, output, mir->isSaturating(), oolEntry);
    else if (fromType == MIRType::Float32)
        masm.wasmTruncateFloat32ToInt32(input, output, mir->isSaturating(), oolEntry);
    else
        MOZ_CRASH("unexpected type");

    masm.bind(ool->rejoin());
}


void
CodeGeneratorPPC64LE::visitOutOfLineBailout(OutOfLineBailout* ool)
{
    ADBlock();

    // Push snapshotOffset and make sure stack is aligned.
    masm.subPtr(Imm32(sizeof(Value)), StackPointer);
    masm.storePtr(ImmWord(ool->snapshot()->snapshotOffset()), Address(StackPointer, 0));

    masm.jump(&deoptLabel_);
}

void
CodeGeneratorPPC64LE::visitOutOfLineWasmTruncateCheck(OutOfLineWasmTruncateCheck* ool)
{
    if(ool->toType() == MIRType::Int32)
    {
        masm.outOfLineWasmTruncateToInt32Check(ool->input(), ool->output(), ool->fromType(),
                                               ool->flags(), ool->rejoin(), ool->bytecodeOffset());
    } else {
        MOZ_ASSERT(ool->toType() == MIRType::Int64);
        masm.outOfLineWasmTruncateToInt64Check(ool->input(), ool->output64(), ool->fromType(),
                                               ool->flags(), ool->rejoin(), ool->bytecodeOffset());
    }
}

void
CodeGenerator::visitCopySignF(LCopySignF* ins)
{
    ADBlock();
    FloatRegister lhs = ToFloatRegister(ins->getOperand(0));
    FloatRegister rhs = ToFloatRegister(ins->getOperand(1));
    FloatRegister output = ToFloatRegister(ins->getDef(0));

// XXX: this probably could be better written
    Register lhsi = ToRegister(ins->getTemp(0));
    Register rhsi = ToRegister(ins->getTemp(1));

    masm.moveFromFloat32(lhs, lhsi);
    masm.moveFromFloat32(rhs, rhsi);

    // Combine.
    masm.ma_ins(rhsi, lhsi, 0, 31);

    masm.moveToFloat32(rhsi, output);
}

void
CodeGenerator::visitCopySignD(LCopySignD* ins)
{
    ADBlock();
    FloatRegister lhs = ToFloatRegister(ins->getOperand(0));
    FloatRegister rhs = ToFloatRegister(ins->getOperand(1));
    FloatRegister output = ToFloatRegister(ins->getDef(0));

// XXX: this probably could be better written
    Register lhsi = ToRegister(ins->getTemp(0));
    Register rhsi = ToRegister(ins->getTemp(1));

    // Manipulate high words of double inputs.
    masm.moveFromDoubleHi(lhs, lhsi);
    masm.moveFromDoubleHi(rhs, rhsi);

    // Combine.
    masm.ma_ins(rhsi, lhsi, 0, 31);

    masm.moveToDoubleHi(rhsi, output);
}

void
CodeGenerator::visitValue(LValue* value)
{
    ADBlock();
    const ValueOperand out = ToOutValue(value);

    masm.moveValue(value->value(), out);
}

void
CodeGenerator::visitDouble(LDouble* ins)
{
    ADBlock();
    const LDefinition* out = ins->getDef(0);

    masm.loadConstantDouble(ins->getDouble(), ToFloatRegister(out));
}

void
CodeGenerator::visitFloat32(LFloat32* ins)
{
    ADBlock();
    const LDefinition* out = ins->getDef(0);
    masm.loadConstantFloat32(ins->getFloat(), ToFloatRegister(out));
}

void
CodeGenerator::visitTestDAndBranch(LTestDAndBranch* test)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(test->input());

    MBasicBlock* ifTrue = test->ifTrue();
    MBasicBlock* ifFalse = test->ifFalse();

    masm.loadConstantDouble(0.0, ScratchDoubleReg);
    // If 0, or NaN, the result is false.

    if (isNextBlock(ifFalse->lir())) {
        branchToBlock(Assembler::DoubleFloat, input, ScratchDoubleReg, ifTrue,
                      Assembler::DoubleNotEqual);
    } else {
        branchToBlock(Assembler::DoubleFloat, input, ScratchDoubleReg, ifFalse,
                      Assembler::DoubleEqualOrUnordered);
        jumpToBlock(ifTrue);
    }
}

void
CodeGenerator::visitTestFAndBranch(LTestFAndBranch* test)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(test->input());

    MBasicBlock* ifTrue = test->ifTrue();
    MBasicBlock* ifFalse = test->ifFalse();

    masm.loadConstantFloat32(0.0f, ScratchFloat32Reg);
    // If 0, or NaN, the result is false.

    if (isNextBlock(ifFalse->lir())) {
        branchToBlock(Assembler::SingleFloat, input, ScratchFloat32Reg, ifTrue,
                      Assembler::DoubleNotEqual);
    } else {
        branchToBlock(Assembler::SingleFloat, input, ScratchFloat32Reg, ifFalse,
                      Assembler::DoubleEqualOrUnordered);
        jumpToBlock(ifTrue);
    }
}

void
CodeGenerator::visitCompareD(LCompareD* comp)
{
    ADBlock();
    FloatRegister lhs = ToFloatRegister(comp->left());
    FloatRegister rhs = ToFloatRegister(comp->right());
    Register dest = ToRegister(comp->output());

    Assembler::DoubleCondition cond = JSOpToDoubleCondition(comp->mir()->jsop());
    masm.ma_cmp_set_double(dest, lhs, rhs, cond);
}

void
CodeGenerator::visitCompareF(LCompareF* comp)
{
    ADBlock();
    FloatRegister lhs = ToFloatRegister(comp->left());
    FloatRegister rhs = ToFloatRegister(comp->right());
    Register dest = ToRegister(comp->output());

    Assembler::DoubleCondition cond = JSOpToDoubleCondition(comp->mir()->jsop());
    masm.ma_cmp_set_float32(dest, lhs, rhs, cond);
}

void
CodeGenerator::visitCompareDAndBranch(LCompareDAndBranch* comp)
{
    ADBlock();
    FloatRegister lhs = ToFloatRegister(comp->left());
    FloatRegister rhs = ToFloatRegister(comp->right());

    Assembler::DoubleCondition cond = JSOpToDoubleCondition(comp->cmpMir()->jsop());
    MBasicBlock* ifTrue = comp->ifTrue();
    MBasicBlock* ifFalse = comp->ifFalse();

    if (isNextBlock(ifFalse->lir())) {
        branchToBlock(Assembler::DoubleFloat, lhs, rhs, ifTrue, cond);
    } else {
        branchToBlock(Assembler::DoubleFloat, lhs, rhs, ifFalse,
                      Assembler::InvertCondition(cond));
        jumpToBlock(ifTrue);
    }
}

void
CodeGenerator::visitCompareFAndBranch(LCompareFAndBranch* comp)
{
    ADBlock();
    FloatRegister lhs = ToFloatRegister(comp->left());
    FloatRegister rhs = ToFloatRegister(comp->right());

    Assembler::DoubleCondition cond = JSOpToDoubleCondition(comp->cmpMir()->jsop());
    MBasicBlock* ifTrue = comp->ifTrue();
    MBasicBlock* ifFalse = comp->ifFalse();

    if (isNextBlock(ifFalse->lir())) {
        branchToBlock(Assembler::SingleFloat, lhs, rhs, ifTrue, cond);
    } else {
        branchToBlock(Assembler::SingleFloat, lhs, rhs, ifFalse,
                      Assembler::InvertCondition(cond));
        jumpToBlock(ifTrue);
    }
}

void
CodeGenerator::visitBitAndAndBranch(LBitAndAndBranch* lir)
{
    ADBlock();
    if (lir->right()->isConstant())
        masm.ma_and(ScratchRegister, ToRegister(lir->left()), Imm32(ToInt32(lir->right())));
    else
        masm.as_and(ScratchRegister, ToRegister(lir->left()), ToRegister(lir->right()));
    emitBranch(ScratchRegister, ScratchRegister, lir->cond(), lir->ifTrue(),
               lir->ifFalse());
}

void
CodeGenerator::visitWasmUint32ToDouble(LWasmUint32ToDouble* lir)
{
    masm.convertUInt32ToDouble(ToRegister(lir->input()), ToFloatRegister(lir->output()));
}

void
CodeGenerator::visitWasmUint32ToFloat32(LWasmUint32ToFloat32* lir)
{
    masm.convertUInt32ToFloat32(ToRegister(lir->input()), ToFloatRegister(lir->output()));
}

void
CodeGenerator::visitNotI(LNotI* ins)
{
    ADBlock();
    masm.cmp32Set(Assembler::Equal, ToRegister(ins->input()), Imm32(0),
                  ToRegister(ins->output()));
}

void
CodeGenerator::visitNotD(LNotD* ins)
{
    ADBlock();
    // Since this operation is not, we want to set a bit if
    // the double is falsey, which means 0.0, -0.0 or NaN.
    FloatRegister in = ToFloatRegister(ins->input());
    Register dest = ToRegister(ins->output());

    masm.loadConstantDouble(0.0, ScratchDoubleReg);
    masm.ma_cmp_set_double(dest, in, ScratchDoubleReg, Assembler::DoubleEqualOrUnordered);
}

void
CodeGenerator::visitNotF(LNotF* ins)
{
    ADBlock();
    // Since this operation is not, we want to set a bit if
    // the float32 is falsey, which means 0.0, -0.0 or NaN.
    FloatRegister in = ToFloatRegister(ins->input());
    Register dest = ToRegister(ins->output());

    masm.loadConstantFloat32(0.0f, ScratchFloat32Reg);
    masm.ma_cmp_set_float32(dest, in, ScratchFloat32Reg, Assembler::DoubleEqualOrUnordered);
}

void
CodeGenerator::visitMemoryBarrier(LMemoryBarrier* ins)
{
    ADBlock();
    masm.memoryBarrier(ins->type());
}

void
CodeGeneratorPPC64LE::generateInvalidateEpilogue()
{
    ADBlock();

    // Ensure that there is enough space in the buffer for the OsiPoint
    // patching to occur. Otherwise, we could overwrite the invalidation
    // epilogue.
    for (size_t i = 0; i < sizeof(void*); i += Assembler::NopSize())
        masm.nop();

    masm.bind(&invalidate_);

    // Push the return address of the point that we bailed out at to the stack
    masm.pushReturnAddress(); // LR

    // Push the Ion script onto the stack (when we determine what that
    // pointer is).
    invalidateEpilogueData_ = masm.pushWithPatch(ImmWord(uintptr_t(-1)));
    TrampolinePtr thunk = gen->jitRuntime()->getInvalidationThunk();

    masm.jump(thunk);

    // We should never reach this point in JIT code -- the invalidation thunk
    // should pop the invalidated JS frame and return directly to its caller.
    masm.assumeUnreachable("Should have returned directly to its caller instead of here.");
}

class js::jit::OutOfLineTableSwitch : public OutOfLineCodeBase<CodeGeneratorPPC64LE>
{
    MTableSwitch* mir_;
    CodeLabel jumpLabel_;

    void accept(CodeGeneratorPPC64LE* codegen) {
        codegen->visitOutOfLineTableSwitch(this);
    }

  public:
    OutOfLineTableSwitch(MTableSwitch* mir)
      : mir_(mir)
    {}

    MTableSwitch* mir() const {
        return mir_;
    }

    CodeLabel* jumpLabel() {
        return &jumpLabel_;
    }
};

void
CodeGeneratorPPC64LE::visitOutOfLineTableSwitch(OutOfLineTableSwitch* ool)
{
    ADBlock();
    MTableSwitch* mir = ool->mir();

    masm.haltingAlign(sizeof(void*));
    masm.bind(ool->jumpLabel());
    masm.addCodeLabel(*ool->jumpLabel());

    for (size_t i = 0; i < mir->numCases(); i++) {
        LBlock* caseblock = skipTrivialBlocks(mir->getCase(i))->lir();
        Label* caseheader = caseblock->label();
        uint32_t caseoffset = caseheader->offset();

        // The entries of the jump table need to be absolute addresses and thus
        // must be patched after codegen is finished.
        CodeLabel cl;
        masm.writeCodePointer(&cl);
        cl.target()->bind(caseoffset);
        masm.addCodeLabel(cl);
    }
}

void
CodeGeneratorPPC64LE::emitTableSwitchDispatch(MTableSwitch* mir, Register index,
                                           Register base)
{
    ADBlock();
    Label* defaultcase = skipTrivialBlocks(mir->getDefault())->lir()->label();

    // Lower value with low value
    if (mir->low() != 0)
        masm.subPtr(Imm32(mir->low()), index);

    // Jump to default case if input is out of range
    int32_t cases = mir->numCases();
    masm.branchPtr(Assembler::AboveOrEqual, index, ImmWord(cases), defaultcase);

    // To fill in the CodeLabels for the case entries, we need to first
    // generate the case entries (we don't yet know their offsets in the
    // instruction stream).
    OutOfLineTableSwitch* ool = new(alloc()) OutOfLineTableSwitch(mir);
    addOutOfLineCode(ool, mir);

    // Compute the position where a pointer to the right case stands.
    masm.ma_li(base, ool->jumpLabel());

    BaseIndex pointer(base, index, ScalePointer);

    // Jump to the right case
    masm.branchToComputedAddress(pointer);
}

template <typename T>
void
CodeGeneratorPPC64LE::emitWasmLoad(T* lir)
{
    ADBlock();
    const MWasmLoad* mir = lir->mir();

    Register ptrScratch = InvalidReg;
    if(!lir->ptrCopy()->isBogusTemp()){
        ptrScratch = ToRegister(lir->ptrCopy());
    }

    if (IsUnaligned(mir->access())) {
        if (IsFloatingPointType(mir->type())) {
            masm.wasmUnalignedLoadFP(mir->access(), HeapReg, ToRegister(lir->ptr()), ptrScratch,
                                     ToFloatRegister(lir->output()), ToRegister(lir->getTemp(1)),
                                     InvalidReg, InvalidReg);
        } else {
            masm.wasmUnalignedLoad(mir->access(), HeapReg, ToRegister(lir->ptr()),
                                   ptrScratch, ToRegister(lir->output()), ToRegister(lir->getTemp(1)));
        }
    } else {
        masm.wasmLoad(mir->access(), HeapReg, ToRegister(lir->ptr()), ptrScratch,
                      ToAnyRegister(lir->output()));
    }
}

void
CodeGenerator::visitWasmLoad(LWasmLoad* lir)
{
    emitWasmLoad(lir);
}

void
CodeGenerator::visitWasmUnalignedLoad(LWasmUnalignedLoad* lir)
{
    emitWasmLoad(lir);
}

template <typename T>
void
CodeGeneratorPPC64LE::emitWasmStore(T* lir)
{
    const MWasmStore* mir = lir->mir();

    Register ptrScratch = InvalidReg;
    if(!lir->ptrCopy()->isBogusTemp()){
        ptrScratch = ToRegister(lir->ptrCopy());
    }

    if (IsUnaligned(mir->access())) {
        if (mir->access().type() == Scalar::Float32 ||
            mir->access().type() == Scalar::Float64) {
            masm.wasmUnalignedStoreFP(mir->access(), ToFloatRegister(lir->value()),
                                      HeapReg, ToRegister(lir->ptr()), ptrScratch,
                                      ToRegister(lir->getTemp(1)));
        } else {
            masm.wasmUnalignedStore(mir->access(), ToRegister(lir->value()), HeapReg,
                                    ToRegister(lir->ptr()), ptrScratch,
                                    ToRegister(lir->getTemp(1)));
        }
    } else {
        masm.wasmStore(mir->access(), ToAnyRegister(lir->value()), HeapReg,
                       ToRegister(lir->ptr()), ptrScratch);
    }
}

void
CodeGenerator::visitWasmStore(LWasmStore* lir)
{
    emitWasmStore(lir);
}

void
CodeGenerator::visitWasmUnalignedStore(LWasmUnalignedStore* lir)
{
    emitWasmStore(lir);
}

void
CodeGenerator::visitAsmJSLoadHeap(LAsmJSLoadHeap* ins)
{
    ADBlock();
    const MAsmJSLoadHeap* mir = ins->mir();
    const LAllocation* ptr = ins->ptr();
    const LDefinition* out = ins->output();
    const LAllocation* boundsCheckLimit = ins->boundsCheckLimit();

    bool isSigned;
    int size;
    bool isFloat = false;
    switch (mir->access().type()) {
      case Scalar::Int8:    isSigned = true;  size =  8; break;
      case Scalar::Uint8:   isSigned = false; size =  8; break;
      case Scalar::Int16:   isSigned = true;  size = 16; break;
      case Scalar::Uint16:  isSigned = false; size = 16; break;
      case Scalar::Int32:   isSigned = true;  size = 32; break;
      case Scalar::Uint32:  isSigned = false; size = 32; break;
      case Scalar::Float64: isFloat  = true;  size = 64; break;
      case Scalar::Float32: isFloat  = true;  size = 32; break;
      default: MOZ_CRASH("unexpected array type");
    }

    if (ptr->isConstant()) {
        MOZ_ASSERT(!mir->needsBoundsCheck());
        int32_t ptrImm = ptr->toConstant()->toInt32();
        MOZ_ASSERT(ptrImm >= 0);
        if (isFloat) {
            if (size == 32) {
                masm.loadFloat32(Address(HeapReg, ptrImm), ToFloatRegister(out));
            } else {
                masm.loadDouble(Address(HeapReg, ptrImm), ToFloatRegister(out));
            }
        }  else {
            masm.ma_load(ToRegister(out), Address(HeapReg, ptrImm),
                         static_cast<LoadStoreSize>(size), isSigned ? SignExtend : ZeroExtend);
        }
        return;
    }

    Register ptrReg = ToRegister(ptr);

    if (!mir->needsBoundsCheck()) {
        if (isFloat) {
            if (size == 32) {
                masm.loadFloat32(BaseIndex(HeapReg, ptrReg, TimesOne), ToFloatRegister(out));
            } else {
                masm.loadDouble(BaseIndex(HeapReg, ptrReg, TimesOne), ToFloatRegister(out));
            }
        } else {
            masm.ma_load(ToRegister(out), BaseIndex(HeapReg, ptrReg, TimesOne),
                         static_cast<LoadStoreSize>(size), isSigned ? SignExtend : ZeroExtend);
        }
        return;
    }

    Label done, outOfRange;
    masm.wasmBoundsCheck(Assembler::AboveOrEqual, ptrReg, ToRegister(boundsCheckLimit),
                         &outOfRange);
    // Offset is ok, let's load value.
    if (isFloat) {
        if (size == 32)
            masm.loadFloat32(BaseIndex(HeapReg, ptrReg, TimesOne), ToFloatRegister(out));
        else
            masm.loadDouble(BaseIndex(HeapReg, ptrReg, TimesOne), ToFloatRegister(out));
    } else {
        masm.ma_load(ToRegister(out), BaseIndex(HeapReg, ptrReg, TimesOne),
                     static_cast<LoadStoreSize>(size), isSigned ? SignExtend : ZeroExtend);
    }
    masm.ma_b(&done, ShortJump);
    masm.bind(&outOfRange);
    // Offset is out of range. Load default values.
    if (isFloat) {
        if (size == 32)
            masm.loadConstantFloat32(float(GenericNaN()), ToFloatRegister(out));
        else
            masm.loadConstantDouble(GenericNaN(), ToFloatRegister(out));
    } else {
        masm.move32(Imm32(0), ToRegister(out));
    }
    masm.bind(&done);
}

void
CodeGenerator::visitAsmJSStoreHeap(LAsmJSStoreHeap* ins)
{
    ADBlock();
    const MAsmJSStoreHeap* mir = ins->mir();
    const LAllocation* value = ins->value();
    const LAllocation* ptr = ins->ptr();
    const LAllocation* boundsCheckLimit = ins->boundsCheckLimit();

    bool isSigned;
    int size;
    bool isFloat = false;
    switch (mir->access().type()) {
      case Scalar::Int8:    isSigned = true;  size =  8; break;
      case Scalar::Uint8:   isSigned = false; size =  8; break;
      case Scalar::Int16:   isSigned = true;  size = 16; break;
      case Scalar::Uint16:  isSigned = false; size = 16; break;
      case Scalar::Int32:   isSigned = true;  size = 32; break;
      case Scalar::Uint32:  isSigned = false; size = 32; break;
      case Scalar::Float64: isFloat  = true;  size = 64; break;
      case Scalar::Float32: isFloat  = true;  size = 32; break;
      default: MOZ_CRASH("unexpected array type");
    }

    if (ptr->isConstant()) {
        MOZ_ASSERT(!mir->needsBoundsCheck());
        int32_t ptrImm = ptr->toConstant()->toInt32();
        MOZ_ASSERT(ptrImm >= 0);

        if (isFloat) {
            FloatRegister freg = ToFloatRegister(value);
            Address addr(HeapReg, ptrImm);
            if (size == 32)
                masm.storeFloat32(freg, addr);
            else
                masm.storeDouble(freg, addr);
        }  else {
            masm.ma_store(ToRegister(value), Address(HeapReg, ptrImm),
                          static_cast<LoadStoreSize>(size), isSigned ? SignExtend : ZeroExtend);
        }
        return;
    }

    Register ptrReg = ToRegister(ptr);
    Address dstAddr(ptrReg, 0);

    if (!mir->needsBoundsCheck()) {
        if (isFloat) {
            FloatRegister freg = ToFloatRegister(value);
            BaseIndex bi(HeapReg, ptrReg, TimesOne);
            if (size == 32)
                masm.storeFloat32(freg, bi);
            else
                masm.storeDouble(freg, bi);
        } else {
            masm.ma_store(ToRegister(value), BaseIndex(HeapReg, ptrReg, TimesOne),
                          static_cast<LoadStoreSize>(size), isSigned ? SignExtend : ZeroExtend);
        }
        return;
    }

    Label outOfRange;
    masm.wasmBoundsCheck(Assembler::AboveOrEqual, ptrReg, ToRegister(boundsCheckLimit),
                         &outOfRange);

    // Offset is ok, let's store value.
    if (isFloat) {
        if (size == 32) {
            masm.storeFloat32(ToFloatRegister(value), BaseIndex(HeapReg, ptrReg, TimesOne));
        } else
            masm.storeDouble(ToFloatRegister(value), BaseIndex(HeapReg, ptrReg, TimesOne));
    } else {
        masm.ma_store(ToRegister(value), BaseIndex(HeapReg, ptrReg, TimesOne),
                      static_cast<LoadStoreSize>(size), isSigned ? SignExtend : ZeroExtend);
    }

    masm.bind(&outOfRange);
}

void
CodeGenerator::visitWasmCompareExchangeHeap(LWasmCompareExchangeHeap* ins)
{
    ADBlock();
    MWasmCompareExchangeHeap* mir = ins->mir();
    Scalar::Type vt = mir->access().type();
    Register ptrReg = ToRegister(ins->ptr());
    BaseIndex srcAddr(HeapReg, ptrReg, TimesOne, mir->access().offset());
    MOZ_ASSERT(ins->addrTemp()->isBogusTemp());

    Register oldval = ToRegister(ins->oldValue());
    Register newval = ToRegister(ins->newValue());
    Register valueTemp = ToTempRegisterOrInvalid(ins->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(ins->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(ins->maskTemp());

    masm.compareExchange(vt, Synchronization::Full(), srcAddr, oldval, newval, valueTemp,
                         offsetTemp, maskTemp, ToRegister(ins->output()));
}

void
CodeGenerator::visitWasmAtomicExchangeHeap(LWasmAtomicExchangeHeap* ins)
{
    ADBlock();
    MWasmAtomicExchangeHeap* mir = ins->mir();
    Scalar::Type vt = mir->access().type();
    Register ptrReg = ToRegister(ins->ptr());
    Register value = ToRegister(ins->value());
    BaseIndex srcAddr(HeapReg, ptrReg, TimesOne, mir->access().offset());
    MOZ_ASSERT(ins->addrTemp()->isBogusTemp());

    Register valueTemp = ToTempRegisterOrInvalid(ins->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(ins->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(ins->maskTemp());

    masm.atomicExchange(vt, Synchronization::Full(), srcAddr, value, valueTemp, offsetTemp,
                        maskTemp, ToRegister(ins->output()));
}

void
CodeGenerator::visitWasmAtomicBinopHeap(LWasmAtomicBinopHeap* ins)
{
    ADBlock();
    MOZ_ASSERT(ins->mir()->hasUses());
    MOZ_ASSERT(ins->addrTemp()->isBogusTemp());

    MWasmAtomicBinopHeap* mir = ins->mir();
    Scalar::Type vt = mir->access().type();
    Register ptrReg = ToRegister(ins->ptr());
    Register valueTemp = ToTempRegisterOrInvalid(ins->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(ins->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(ins->maskTemp());

    BaseIndex srcAddr(HeapReg, ptrReg, TimesOne, mir->access().offset());

    masm.atomicFetchOp(vt, Synchronization::Full(), mir->operation(), ToRegister(ins->value()),
                       srcAddr, valueTemp, offsetTemp, maskTemp, ToRegister(ins->output()));
}

void
CodeGenerator::visitWasmAtomicBinopHeapForEffect(LWasmAtomicBinopHeapForEffect* ins)
{
    ADBlock();
    MOZ_ASSERT(!ins->mir()->hasUses());
    MOZ_ASSERT(ins->addrTemp()->isBogusTemp());

    MWasmAtomicBinopHeap* mir = ins->mir();
    Scalar::Type vt = mir->access().type();
    Register ptrReg = ToRegister(ins->ptr());
    Register valueTemp = ToTempRegisterOrInvalid(ins->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(ins->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(ins->maskTemp());

    BaseIndex srcAddr(HeapReg, ptrReg, TimesOne, mir->access().offset());
    masm.atomicEffectOp(vt, Synchronization::Full(), mir->operation(), ToRegister(ins->value()),
                        srcAddr, valueTemp, offsetTemp, maskTemp);
}

void
CodeGenerator::visitWasmStackArg(LWasmStackArg* ins)
{
    ADBlock();
    const MWasmStackArg* mir = ins->mir();
    if (ins->arg()->isConstant()) {
        masm.storePtr(ImmWord(ToInt32(ins->arg())), Address(StackPointer, mir->spOffset()));
    } else {
        if (ins->arg()->isGeneralReg()) {
            masm.storePtr(ToRegister(ins->arg()), Address(StackPointer, mir->spOffset()));
        } else if (mir->input()->type() == MIRType::Double) {
            masm.storeDouble(ToFloatRegister(ins->arg()).doubleOverlay(),
                             Address(StackPointer, mir->spOffset()));
        } else {
            masm.storeFloat32(ToFloatRegister(ins->arg()),
                             Address(StackPointer, mir->spOffset()));
        }
    }
}

void
CodeGenerator::visitWasmStackArgI64(LWasmStackArgI64* ins)
{
    ADBlock();
    const MWasmStackArg* mir = ins->mir();
    Address dst(StackPointer, mir->spOffset());
    if (IsConstant(ins->arg()))
        masm.store64(Imm64(ToInt64(ins->arg())), dst);
    else
        masm.store64(ToRegister64(ins->arg()), dst);
}

void
CodeGenerator::visitWasmSelect(LWasmSelect* ins)
{
    ADBlock();
    MIRType mirType = ins->mir()->type();

    Register cond = ToRegister(ins->condExpr());
    const LAllocation* falseExpr = ins->falseExpr();

    if (mirType == MIRType::Int32) {
        Register out = ToRegister(ins->output());
        MOZ_ASSERT(ToRegister(ins->trueExpr()) == out, "true expr input is reused for output");
        masm.as_cmpi(cond, 0);
        masm.as_isel(out, out, ToRegister(falseExpr), 2); // CR0[EQ]
        return;
    }

    FloatRegister out = ToFloatRegister(ins->output());
    MOZ_ASSERT(ToFloatRegister(ins->trueExpr()) == out, "true expr input is reused for output");

    // We can't use fsel because cond isn't a float register.
    Label done;
    masm.ma_b(cond, cond, &done, Assembler::NonZero, ShortJump);

    if (mirType == MIRType::Float32)
        masm.loadFloat32(ToAddress(falseExpr), out);
    else if (mirType == MIRType::Double)
        masm.loadDouble(ToAddress(falseExpr), out);
    else
        MOZ_CRASH("unhandled type in visitWasmSelect!");

    masm.bind(&done);
}

void
CodeGenerator::visitWasmReinterpret(LWasmReinterpret* lir)
{
    ADBlock();
    MOZ_ASSERT(gen->compilingWasm());
    MWasmReinterpret* ins = lir->mir();

    MIRType to = ins->type();
    DebugOnly<MIRType> from = ins->input()->type();

    switch (to) {
      // We don't have much choice other than to spill to memory for these.
      case MIRType::Int32:
        MOZ_ASSERT(from == MIRType::Float32);
        masm.as_stfsu(ToFloatRegister(lir->input()), StackPointer, -4);
        // Keep in separate dispatch groups.
        masm.nop();
        masm.nop();
        masm.nop();
        masm.as_lwz(ToRegister(lir->output()), StackPointer, 0);
        masm.as_addi(StackPointer, StackPointer, 4);
        break;
      case MIRType::Float32:
        MOZ_ASSERT(from == MIRType::Int32);
        masm.as_stwu(ToRegister(lir->input()), StackPointer, -4);
        // Keep in separate dispatch groups.
        masm.nop();
        masm.nop();
        masm.nop();
        masm.as_lfs(ToFloatRegister(lir->output()), StackPointer, 0);
        masm.as_addi(StackPointer, StackPointer, 4);
        break;
      case MIRType::Double:
      case MIRType::Int64:
        MOZ_CRASH("not handled by this LIR opcode");
      default:
        MOZ_CRASH("unexpected WasmReinterpret");
    }
}

void
CodeGenerator::visitUDivOrMod(LUDivOrMod* ins)
{
    ADBlock();
    Register lhs = ToRegister(ins->lhs());
    Register rhs = ToRegister(ins->rhs());
    Register output = ToRegister(ins->output());
    Label done;

    // Although divwuo can flag overflow for divide by zero, we end up
    // checking anyway to deal with the Infinity|0 situation, so we just don't
    // bother and use regular (cheaper) divwu.
    if (ins->canBeDivideByZero()) {
        if (ins->mir()->isTruncated()) {
            if (ins->trapOnError()) {
                Label nonZero;
                masm.ma_b(rhs, rhs, &nonZero, Assembler::NonZero);
                masm.wasmTrap(wasm::Trap::IntegerDivideByZero, ins->bytecodeOffset());
                masm.bind(&nonZero);
            } else {
                // Infinity|0 == 0
                Label notzero;
                masm.ma_b(rhs, rhs, &notzero, Assembler::NonZero, ShortJump);
                masm.move32(Imm32(0), output);
                masm.ma_b(&done, ShortJump);
                masm.bind(&notzero);
            }
        } else {
            bailoutCmp32(Assembler::Equal, rhs, Imm32(0), ins->snapshot());
        }
    }

    // If the remainder is > 0, bailout since this must be a double.
    if (ins->mir()->isDiv()) {
        // Compute quotient to output register; separately recover remainder.
        masm.as_divwu(output, lhs, rhs);
        masm.as_mullw(SecondScratchReg, output, rhs);
        masm.as_subf(ScratchRegister, SecondScratchReg, lhs); // T = B - A
        if (!ins->mir()->toDiv()->canTruncateRemainder())
          bailoutCmp32(Assembler::NonZero, ScratchRegister, ScratchRegister, ins->snapshot());
    } else {
        // Compute remainder to output register.
        masm.as_divwu(ScratchRegister, lhs, rhs);
        masm.as_mullw(SecondScratchReg, ScratchRegister, rhs);
        masm.as_subf(output, SecondScratchReg, lhs);
    }

    if (!ins->mir()->isTruncated())
        bailoutCmp32(Assembler::LessThan, output, Imm32(0), ins->snapshot());

    masm.bind(&done);
}

void
CodeGenerator::visitEffectiveAddress(LEffectiveAddress* ins)
{
    ADBlock();
    const MEffectiveAddress* mir = ins->mir();
    Register base = ToRegister(ins->base());
    Register index = ToRegister(ins->index());
    Register output = ToRegister(ins->output());

    BaseIndex address(base, index, mir->scale(), mir->displacement());
    masm.computeEffectiveAddress(address, output);
}

void
CodeGenerator::visitNegI(LNegI* ins)
{
    ADBlock();
    Register input = ToRegister(ins->input());
    Register output = ToRegister(ins->output());

    masm.as_neg(output, input);
}

void
CodeGenerator::visitNegD(LNegD* ins)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    FloatRegister output = ToFloatRegister(ins->output());

    masm.as_fneg(output, input);
}

void
CodeGenerator::visitNegF(LNegF* ins)
{
    ADBlock();
    FloatRegister input = ToFloatRegister(ins->input());
    FloatRegister output = ToFloatRegister(ins->output());

    masm.as_fneg(output, input);
}

void
CodeGenerator::visitWasmAddOffset(LWasmAddOffset* lir)
{
    ADBlock();
    MWasmAddOffset* mir = lir->mir();
    Register base = ToRegister(lir->base());
    Register out = ToRegister(lir->output());

    Label ok;
    masm.ma_addTestCarry(Assembler::CarryClear, out, base, Imm32(mir->offset()), &ok);
    masm.wasmTrap(wasm::Trap::OutOfBounds, mir->bytecodeOffset());
    masm.bind(&ok);
}


void
CodeGenerator::visitAtomicTypedArrayElementBinop(LAtomicTypedArrayElementBinop* lir)
{
    ADBlock();
    MOZ_ASSERT(lir->mir()->hasUses());

    AnyRegister output = ToAnyRegister(lir->output());
    Register elements = ToRegister(lir->elements());
    Register outTemp = ToTempRegisterOrInvalid(lir->temp2());
    Register valueTemp = ToTempRegisterOrInvalid(lir->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(lir->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(lir->maskTemp());
    Register value = ToRegister(lir->value());

    Scalar::Type arrayType = lir->mir()->arrayType();
    int width = Scalar::byteSize(arrayType);

    if (lir->index()->isConstant()) {
        Address mem(elements, ToInt32(lir->index()) * width);
        masm.atomicFetchOpJS(arrayType, Synchronization::Full(), lir->mir()->operation(), value,
                             mem, valueTemp, offsetTemp, maskTemp, outTemp, output);
    } else {
        BaseIndex mem(elements, ToRegister(lir->index()), ScaleFromElemWidth(width));
        masm.atomicFetchOpJS(arrayType, Synchronization::Full(), lir->mir()->operation(), value,
                             mem, valueTemp, offsetTemp, maskTemp, outTemp, output);
    }
}

void
CodeGenerator::visitAtomicTypedArrayElementBinopForEffect(LAtomicTypedArrayElementBinopForEffect* lir)
{
    ADBlock();
    MOZ_ASSERT(!lir->mir()->hasUses());

    Register elements = ToRegister(lir->elements());
    Register valueTemp = ToTempRegisterOrInvalid(lir->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(lir->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(lir->maskTemp());
    Register value = ToRegister(lir->value());
    Scalar::Type arrayType = lir->mir()->arrayType();
    int width = Scalar::byteSize(arrayType);

    if (lir->index()->isConstant()) {
        Address mem(elements, ToInt32(lir->index()) * width);
        masm.atomicEffectOpJS(arrayType, Synchronization::Full(), lir->mir()->operation(), value,
                             mem, valueTemp, offsetTemp, maskTemp);
    } else {
        BaseIndex mem(elements, ToRegister(lir->index()), ScaleFromElemWidth(width));
        masm.atomicEffectOpJS(arrayType, Synchronization::Full(), lir->mir()->operation(), value,
                             mem, valueTemp, offsetTemp, maskTemp);
    }
}

void
CodeGenerator::visitCompareExchangeTypedArrayElement(LCompareExchangeTypedArrayElement* lir)
{
    ADBlock();
    Register elements = ToRegister(lir->elements());
    AnyRegister output = ToAnyRegister(lir->output());
    Register outTemp = ToTempRegisterOrInvalid(lir->temp());

    Register oldval = ToRegister(lir->oldval());
    Register newval = ToRegister(lir->newval());
    Register valueTemp = ToTempRegisterOrInvalid(lir->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(lir->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(lir->maskTemp());

    Scalar::Type arrayType = lir->mir()->arrayType();
    int width = Scalar::byteSize(arrayType);

    if (lir->index()->isConstant()) {
        Address dest(elements, ToInt32(lir->index()) * width);
        masm.compareExchangeJS(arrayType, Synchronization::Full(), dest, oldval, newval,
                               valueTemp, offsetTemp, maskTemp, outTemp, output);
    } else {
        BaseIndex dest(elements, ToRegister(lir->index()), ScaleFromElemWidth(width));
        masm.compareExchangeJS(arrayType, Synchronization::Full(), dest, oldval, newval,
                               valueTemp, offsetTemp, maskTemp, outTemp, output);
    }
}

void
CodeGenerator::visitAtomicExchangeTypedArrayElement(LAtomicExchangeTypedArrayElement* lir)
{
    ADBlock();
    Register elements = ToRegister(lir->elements());
    AnyRegister output = ToAnyRegister(lir->output());
    Register outTemp = ToTempRegisterOrInvalid(lir->temp());

    Register value = ToRegister(lir->value());
    Register valueTemp = ToTempRegisterOrInvalid(lir->valueTemp());
    Register offsetTemp = ToTempRegisterOrInvalid(lir->offsetTemp());
    Register maskTemp = ToTempRegisterOrInvalid(lir->maskTemp());

    Scalar::Type arrayType = lir->mir()->arrayType();
    int width = Scalar::byteSize(arrayType);

    if (lir->index()->isConstant()) {
        Address dest(elements, ToInt32(lir->index()) * width);
        masm.atomicExchangeJS(arrayType, Synchronization::Full(), dest, value, valueTemp,
                              offsetTemp, maskTemp, outTemp, output);
    } else {
        BaseIndex dest(elements, ToRegister(lir->index()), ScaleFromElemWidth(width));
        masm.atomicExchangeJS(arrayType, Synchronization::Full(), dest, value, valueTemp,
                              offsetTemp, maskTemp, outTemp, output);
    }
}

void
CodeGenerator::visitWasmCompareExchangeI64(LWasmCompareExchangeI64* lir)
{
    ADBlock();
    Register ptr = ToRegister(lir->ptr());
    Register64 oldValue = ToRegister64(lir->oldValue());
    Register64 newValue = ToRegister64(lir->newValue());
    Register64 output = ToOutRegister64(lir);
    uint32_t offset = lir->mir()->access().offset();

    BaseIndex addr(HeapReg, ptr, TimesOne, offset);
    masm.compareExchange64(Synchronization::Full(), addr, oldValue, newValue, output);
}

void
CodeGenerator::visitWasmAtomicExchangeI64(LWasmAtomicExchangeI64* lir)
{
    ADBlock();
    Register ptr = ToRegister(lir->ptr());
    Register64 value = ToRegister64(lir->value());
    Register64 output = ToOutRegister64(lir);
    uint32_t offset = lir->mir()->access().offset();

    BaseIndex addr(HeapReg, ptr, TimesOne, offset);
    masm.atomicExchange64(Synchronization::Full(), addr, value, output);
}

void
CodeGenerator::visitWasmAtomicBinopI64(LWasmAtomicBinopI64* lir)
{
    ADBlock();
    Register ptr = ToRegister(lir->ptr());
    Register64 value = ToRegister64(lir->value());
    Register64 output = ToOutRegister64(lir);
    Register64 temp(ToRegister(lir->getTemp(0)));
    uint32_t offset = lir->mir()->access().offset();

    BaseIndex addr(HeapReg, ptr, TimesOne, offset);

    masm.atomicFetchOp64(Synchronization::Full(), lir->mir()->operation(), value, addr, temp,
                         output);
}

void
CodeGenerator::visitSimdSplatX4(LSimdSplatX4* lir)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimd128Int(LSimd128Int* ins)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimd128Float(LSimd128Float* ins)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdExtractElementI(LSimdExtractElementI* ins)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdExtractElementF(LSimdExtractElementF* ins)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryCompIx4(LSimdBinaryCompIx4* lir)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryCompFx4(LSimdBinaryCompFx4* lir)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryArithIx4(LSimdBinaryArithIx4* lir)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryArithFx4(LSimdBinaryArithFx4* lir)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryBitwise(LSimdBinaryBitwise* lir)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitNearbyInt(LNearbyInt*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdShift(LSimdShift*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitNearbyIntF(LNearbyIntF*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdSelect(LSimdSelect*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdAllTrue(LSimdAllTrue*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdAnyTrue(LSimdAnyTrue*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdShuffle(LSimdShuffle*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdSplatX8(LSimdSplatX8*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdSplatX16(LSimdSplatX16*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdSwizzleF(LSimdSwizzleF*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdSwizzleI(LSimdSwizzleI*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdShuffleX4(LSimdShuffleX4*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryCompIx8(LSimdBinaryCompIx8*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdUnaryArithFx4(LSimdUnaryArithFx4*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdUnaryArithIx4(LSimdUnaryArithIx4*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdUnaryArithIx8(LSimdUnaryArithIx8*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitFloat32x4ToInt32x4(LFloat32x4ToInt32x4*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitInt32x4ToFloat32x4(LInt32x4ToFloat32x4*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryArithIx8(LSimdBinaryArithIx8*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryCompIx16(LSimdBinaryCompIx16*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdInsertElementF(LSimdInsertElementF*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdInsertElementI(LSimdInsertElementI*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdUnaryArithIx16(LSimdUnaryArithIx16*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitFloat32x4ToUint32x4(LFloat32x4ToUint32x4*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinaryArithIx16(LSimdBinaryArithIx16*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdExtractElementB(LSimdExtractElementB*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdGeneralShuffleF(LSimdGeneralShuffleF*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdGeneralShuffleI(LSimdGeneralShuffleI*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdReinterpretCast(LSimdReinterpretCast*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdBinarySaturating(LSimdBinarySaturating*)
{
    MOZ_CRASH("NYI");
}

void
CodeGenerator::visitSimdExtractElementU2D(LSimdExtractElementU2D*)
{
    MOZ_CRASH("NYI");
}
