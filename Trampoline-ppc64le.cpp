/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "mozilla/DebugOnly.h"

#include "jit/Bailouts.h"
#include "jit/JitFrames.h"
#include "jit/JitRealm.h"
#include "jit/JitSpewer.h"
#include "jit/Linker.h"
#include "jit/ppc64le/SharedICHelpers-ppc64le.h"
#include "jit/ppc64le/Bailouts-ppc64le.h"
#ifdef JS_ION_PERF
# include "jit/PerfSpewer.h"
#endif
#include "jit/VMFunctions.h"
#include "vm/Realm.h"

#include "jit/MacroAssembler-inl.h"
#include "jit/SharedICHelpers-inl.h"

#if DEBUG

/* Useful class to print visual guard blocks. */
class AutoDeBlock
{
    private:
        const char *blockname;

    public:
        AutoDeBlock(const char *name) {
            blockname = name;
            JitSpew(JitSpew_Codegen, "[[[[[[[[ Trampoline: %s", blockname);
        }

        ~AutoDeBlock() {
            JitSpew(JitSpew_Codegen, "         Trampoline: %s ]]]]]]]]", blockname);
        }
};

#define ADBlock(x)  AutoDeBlock _adbx(x)
            
#else

/* Useful preprocessor macros to completely elide visual guard blocks. */

#define ADBlock(x)  ;

#endif

using namespace js;
using namespace js::jit;

// All registers to save and restore. This includes the stack pointer, since we
// use the ability to reference register values on the stack by index.
static const LiveRegisterSet AllRegs =
    LiveRegisterSet(GeneralRegisterSet(Registers::AllMask),
                         FloatRegisterSet(FloatRegisters::AllMask));

// This trampoline adheres to the PowerPC ELF64 ABI.
static_assert(sizeof(uintptr_t) == sizeof(uint64_t), "Not 32-bit clean.");

/*

From http://refspecs.linuxfoundation.org/ELF/ppc64/PPC-elf64abi.html#FUNC-CALL :

"Registers r1 [SP], r14 through r31, and f14 through f31 are nonvolatile."
"The condition code register fields CR0, CR1, CR5, CR6, and CR7 are volatile."
"Registers r0, r3 through r12, f0 through f13, and the special purpose registers LR, CTR,
XER, and FPSCR are volatile."
"Furthermore, registers r0, r2, r11, and r12 may be modified by cross-module calls."

Figure 3-17. Stack Frame Organization
(marked up with our values)

High Address

          +-> Back chain (SP + 416)
          |   Floating point register save area (SP + 272) (18dw here for f14-f31)
          |   General register save area (SP + 128) (18dw here for r14-r31)
          |   VRSAVE save word (32 bits) (SP + 124)
          |   Alignment padding (4 or 12 bytes) (SP + 112) (12b here)
          |   Vector register save area (quadword aligned) (SP + 112) (not used)
          |   Local variable space   (SP + 112) (not used)
          |   Parameter save area    (SP + 48) (fixed size minimum 8dw here)
          |   TOC save area          (SP + 40)
          |   link editor doubleword (SP + 32)
          |   compiler doubleword    (SP + 24)
          |   LR save area           (SP + 16)
          |   CR save area           (SP + 8)
SP  --->  +-- Back chain             (SP + 0)

Low Address

"The stack pointer shall maintain quadword alignment."

*/

struct EnterJITRegs
{
// SP + 0
    uint64_t sp;
    uint64_t cr;
    uint64_t lr;

    uint64_t comp;
    uint64_t le;
    uint64_t toc;

    uint64_t parameters[7];

// SP + 112
// We cheat here: this is a safe place to store our old VP.
// In the ABI definition this is just padding.
    uint64_t savedvp;
    uint32_t padding;
    uint32_t vrsave;

// SP + 128
    uint64_t r14;
    uint64_t r15;
    uint64_t r16;
    uint64_t r17;
    uint64_t r18;
    uint64_t r19;
    uint64_t r20;
    uint64_t r21;
    uint64_t r22;
    uint64_t r23;
    uint64_t r24;
    uint64_t r25;
    uint64_t r26;
    uint64_t r27;
    uint64_t r28;
    uint64_t r29;
    uint64_t r30;
    uint64_t r31;

    double f14;
    double f15;
    double f16;
    double f17;
    double f18;
    double f19;
    double f20;
    double f21;
    double f22;
    double f23;
    double f24;
    double f25;
    double f26;
    double f27;
    double f28;
    double f29;
    double f30;
    double f31;
// SP + 416
};

static_assert(sizeof(EnterJITRegs) == 416, "Unexpected size of register save frame");
static_assert(offsetof(EnterJITRegs, sp) == 0, "Register save frame is incorrectly oriented");

// Generates a trampoline for calling JIT code from a C++ function.
// The signature is
// EnterJitCode(void* code, unsigned argc, Value* argv, InterpreterFrame* fp,
//              CalleeToken calleeToken, JSObject* envChain,
//              size_t numStackValues, Value* vp);
// Happily, this all fits into registers.
void
JitRuntime::generateEnterJIT(JSContext* cx, MacroAssembler& masm)
{
    ADBlock("generateEnterJIT");
    enterJITOffset_ = startTrampolineCode(masm);

    const Register reg_code = IntArgReg0; // r3
    const Register reg_argc = IntArgReg1; // r4
    const Register reg_argv = IntArgReg2; // r5
    const mozilla::DebugOnly<Register> reg_frame = IntArgReg3; // r6
    const Register reg_token = IntArgReg4; // r7
    const Register reg_chain = IntArgReg5; // r8
    const Register reg_values = IntArgReg6; // r9
    const Register reg_vp = IntArgReg7; // r10

    MOZ_ASSERT(OsrFrameReg == reg_frame);

    // Standard Power prologue, more or less.
    // First save LR and CR to the caller linkage area.
    masm.xs_mflr(ScratchRegister);
    masm.as_std(ScratchRegister, StackPointer, offsetof(EnterJITRegs, lr)); // caller
    masm.as_mfcr(ScratchRegister);
    masm.as_std(ScratchRegister, StackPointer, offsetof(EnterJITRegs, cr)); // caller
    // Save SP to the caller linkage area and pull down the new frame.
    masm.as_stdu(StackPointer, StackPointer, -((uint16_t)sizeof(EnterJITRegs)));

    // Save non-volatile registers.
#define SAVE(x) masm.as_std(x, StackPointer, offsetof(EnterJITRegs, x));
    SAVE(r14)
    SAVE(r15)
    SAVE(r16)
    SAVE(r17)
    SAVE(r18)
    SAVE(r19)
    SAVE(r20)
    SAVE(r21)
    SAVE(r22)
    SAVE(r23)
    SAVE(r24)
    SAVE(r25)
    SAVE(r26)
    SAVE(r27)
    SAVE(r28)
    SAVE(r29)
    SAVE(r30)
    SAVE(r31)
#define SAVE(x) masm.as_stfd(x, StackPointer, offsetof(EnterJITRegs, x));
    SAVE(f14)
    SAVE(f15)
    SAVE(f16)
    SAVE(f17)
    SAVE(f18)
    SAVE(f19)
    SAVE(f20)
    SAVE(f21)
    SAVE(f22)
    SAVE(f23)
    SAVE(f24)
    SAVE(f25)
    SAVE(f26)
    SAVE(f27)
    SAVE(f28)
    SAVE(f29)
    SAVE(f30)
    SAVE(f31)
#undef SAVE

    // Save VP for the end.
    // We would also save VRSAVE here, if we were likely to use VMX/VSX.
    masm.as_std(reg_vp, StackPointer, offsetof(EnterJITRegs, savedvp)); 

    // Hold stack pointer in a random clobberable register for computing
    // the frame descriptor later. Arbitrarily, let's choose r31.
    const Register frameDescSP = r31;
    masm.movePtr(StackPointer, frameDescSP);

    // Save stack pointer as baseline frame.
    masm.movePtr(StackPointer, BaselineFrameReg);

    /***************************************************************
    Loop over argv vector, push arguments onto stack in reverse order
    ***************************************************************/

    // if we are constructing, the count also needs to include newTarget.
    MOZ_ASSERT(CalleeToken_FunctionConstructing == 0x01);
    masm.as_andi_rc(ScratchRegister, reg_token, CalleeToken_FunctionConstructing);
    masm.as_add(reg_argc, reg_argc, ScratchRegister);

    // |Value| is 8-byte aligned, but we want to maintain 16-byte alignment,
    // so tack on an extra Value if the number of arguments is odd.
    // Set the address to copy from to *vp + (argc * 8).
    // WARNING: ABI compliant stack frames are now no longer guaranteed.
    MOZ_ASSERT(sizeof(Value) == 8);
    masm.as_andi_rc(ScratchRegister, reg_argc, 1);
    masm.xs_slwi(SecondScratchReg, reg_argc, 3); // times 8
    masm.xs_slwi(ScratchRegister, ScratchRegister, 3); // times 8
    masm.addPtr(reg_argv, SecondScratchReg);
    masm.add(StackPointer, StackPointer, ScratchRegister);

    // Loop over arguments, copying them from the JS buffer onto the Ion
    // stack so they can be accessed from JIT'ed code.
    Label header, footer;
    // If there aren't any arguments, don't do anything.
    masm.ma_b(SecondScratchReg, reg_argv, &footer, Assembler::BelowOrEqual, ShortJump);
    {
        masm.bind(&header);

        masm.subPtr(Imm32(sizeof(Value)), SecondScratchReg);
        masm.subPtr(Imm32(sizeof(Value)), StackPointer);

        // Because we know we are aligned to at least doubleword, it's safe
        // to use FPU loads and stores and not clobber any GPR argregs yet.
        masm.as_lfd(f0, SecondScratchReg, 0);
        // XXX: Is this usually on stack? Would inserting nops here help?
        masm.as_stfd(f0, StackPointer, 0);

        masm.ma_b(SecondScratchReg, reg_argv, &header, Assembler::Above, ShortJump);
    }
    masm.bind(&footer);

    masm.subPtr(Imm32(2 * sizeof(uintptr_t)), StackPointer);
    // Load the number of actual arguments.
    // This is a 32-bit quantity.
    // Then store it and the callee token on the stack.
    masm.as_lwz(ScratchReg, reg_vp, 0);
    masm.storePtr(reg_token, Address(StackPointer, 0)); // callee token
    masm.storePtr(ScratchReg, Address(StackPointer, sizeof(uintptr_t))); // actual arguments

    // Push frame descriptor.
    masm.subPtr(StackPointer, frameDescSP);
    masm.makeFrameDescriptor(frameDescSP, JitFrame_CppToJSJit, JitFrameLayout::Size());
    masm.push(frameDescSP);

    CodeLabel returnLabel;
    CodeLabel oomReturnLabel;
    {
        // Handle Interpreter -> Baseline OSR.
        AllocatableGeneralRegisterSet regs(GeneralRegisterSet::All());
        regs.take(OsrFrameReg);
        regs.take(BaselineFrameReg);
        regs.take(reg_code);
        regs.take(ReturnReg);
        regs.take(JSReturnOperand);

        Label notOsr;
        masm.ma_b(OsrFrameReg, OsrFrameReg, &notOsr, Assembler::Zero, ShortJump);

        Register numStackValues = reg_values;
        regs.take(numStackValues);
        Register scratch = regs.takeAny();

        // Push return address.
        masm.subPtr(Imm32(sizeof(uintptr_t)), StackPointer);
        masm.ma_li(scratch, &returnLabel);
        masm.storePtr(scratch, Address(StackPointer, 0));

        // Push previous frame pointer.
        masm.subPtr(Imm32(sizeof(uintptr_t)), StackPointer);
        masm.storePtr(BaselineFrameReg, Address(StackPointer, 0));

        // Reserve frame.
        Register framePtr = BaselineFrameReg;
        masm.subPtr(Imm32(BaselineFrame::Size()), StackPointer);
        masm.movePtr(StackPointer, framePtr);

        // Reserve space for locals and stack values.
        masm.xs_sldi(scratch, numStackValues, Imm32(3));
        masm.subPtr(scratch, StackPointer);

        // Enter exit frame.
        masm.addPtr(Imm32(BaselineFrame::Size() + BaselineFrame::FramePointerOffset), scratch);
        masm.makeFrameDescriptor(scratch, JitFrame_BaselineJS, ExitFrameLayout::Size());

        // Push frame descriptor and fake return address.
        masm.reserveStack(2 * sizeof(uintptr_t));
        masm.storePtr(scratch, Address(StackPointer, sizeof(uintptr_t))); // Frame descriptor
        masm.storePtr(zero, Address(StackPointer, 0)); // fake return address

        // No GC things to mark, so push a bare token.
        masm.loadJSContext(scratch);
        masm.enterFakeExitFrame(scratch, scratch, ExitFrameType::Bare);

        masm.reserveStack(2 * sizeof(uintptr_t));
        masm.storePtr(framePtr, Address(StackPointer, sizeof(uintptr_t))); // BaselineFrame
        masm.storePtr(reg_code, Address(StackPointer, 0)); // jitcode

        masm.setupUnalignedABICall(scratch);
        masm.passABIArg(BaselineFrameReg); // BaselineFrame
        masm.passABIArg(OsrFrameReg); // InterpreterFrame
        masm.passABIArg(numStackValues);
        masm.callWithABI(JS_FUNC_TO_DATA_PTR(void*, jit::InitBaselineFrameForOsr), MoveOp::GENERAL,
                         CheckUnsafeCallWithABI::DontCheckHasExitFrame);

        regs.add(OsrFrameReg);
        Register jitcode = regs.takeAny();
        masm.loadPtr(Address(StackPointer, 0), jitcode);
        masm.loadPtr(Address(StackPointer, sizeof(uintptr_t)), framePtr);
        masm.freeStack(2 * sizeof(uintptr_t));

        Label error;
        masm.freeStack(ExitFrameLayout::SizeWithFooter());
        masm.addPtr(Imm32(BaselineFrame::Size()), framePtr);
        masm.branchIfFalseBool(ReturnReg, &error);

        // If OSR-ing, then emit instrumentation for setting lastProfilerFrame
        // if profiler instrumentation is enabled.
        {
            Label skipProfilingInstrumentation;
            Register realFramePtr = numStackValues;
            AbsoluteAddress addressOfEnabled(cx->runtime()->geckoProfiler().addressOfEnabled());
            masm.branch32(Assembler::Equal, addressOfEnabled, Imm32(0),
                          &skipProfilingInstrumentation);
            masm.as_addi(realFramePtr, framePtr, sizeof(void*));
            masm.profilerEnterFrame(realFramePtr, scratch);
            masm.bind(&skipProfilingInstrumentation);
        }

        masm.jump(jitcode);

        // OOM: load error value, discard return address and previous frame
        // pointer and return.
        masm.bind(&error);
        masm.movePtr(framePtr, StackPointer);
        masm.addPtr(Imm32(2 * sizeof(uintptr_t)), StackPointer);
        masm.moveValue(MagicValue(JS_ION_ERROR), JSReturnOperand);
        masm.ma_li(scratch, &oomReturnLabel);
        masm.jump(scratch);

        masm.bind(&notOsr);
        // Load the scope chain in R1.
        MOZ_ASSERT(R1.scratchReg() != reg_code);
        masm.ma_move(R1.scratchReg(), reg_chain);
    }

    // The call will push the return address on the stack, thus we check that
    // the stack would be aligned once the call is complete.
    masm.assertStackAlignment(JitStackAlignment, 16);

    // Call the function with pushing return address to stack.
    masm.callJitNoProfiler(reg_code);

    {
        // Interpreter -> Baseline OSR will return here.
        masm.bind(&returnLabel);
        masm.addCodeLabel(returnLabel);
        masm.bind(&oomReturnLabel);
        masm.addCodeLabel(oomReturnLabel);
    }

    // Pop arguments off the stack.
    // scratch <- 8*argc (size of all arguments we pushed on the stack)
    masm.pop(ScratchReg);
    masm.rshiftPtr(Imm32(FRAMESIZE_SHIFT), ScratchReg);
    masm.addPtr(ScratchReg, StackPointer);

    // Store the returned value into the vp.
    masm.as_ld(reg_vp, StackPointer, offsetof(EnterJITRegs, savedvp));
    masm.storeValue(JSReturnOperand, Address(reg_vp, 0));

    // Restore non-volatile registers and return.
    // Standard PowerPC epilogue, more or less.
    // Load registers.
#define LOAD(x) masm.as_ld(x, StackPointer, offsetof(EnterJITRegs, x));
    LOAD(r14)
    LOAD(r15)
    LOAD(r16)
    LOAD(r17)
    LOAD(r18)
    LOAD(r19)
    LOAD(r20)
    LOAD(r21)
    LOAD(r22)
    LOAD(r23)
    LOAD(r24)
    LOAD(r25)
    LOAD(r26)
    LOAD(r27)
    LOAD(r28)
    LOAD(r29)
    LOAD(r30)
    LOAD(r31)
#define LOAD(x) masm.as_lfd(x, StackPointer, offsetof(EnterJITRegs, x));
    LOAD(f14)
    LOAD(f15)
    LOAD(f16)
    LOAD(f17)
    LOAD(f18)
    LOAD(f19)
    LOAD(f20)
    LOAD(f21)
    LOAD(f22)
    LOAD(f23)
    LOAD(f24)
    LOAD(f25)
    LOAD(f26)
    LOAD(f27)
    LOAD(f28)
    LOAD(f29)
    LOAD(f30)
    LOAD(f31)
#undef LOAD

    // Tear down frame and retrieve the saved LR and CR from the caller's linkage area.
    masm.as_addi(StackPointer, StackPointer, (uint16_t)sizeof(EnterJITRegs));
    masm.as_ld(ScratchRegister, StackPointer, offsetof(EnterJITRegs, lr)); // caller
    masm.xs_mtlr(ScratchRegister);
    masm.as_ld(ScratchRegister, StackPointer, offsetof(EnterJITRegs, cr)); // caller
    masm.as_mfcr(ScratchRegister);

    // Bye!
    masm.as_blr();
}

void
JitRuntime::generateInvalidator(MacroAssembler& masm, Label* bailoutTail)
{
    ADBlock("generateInvalidator");
    invalidatorOffset_ = startTrampolineCode(masm);

    // Stack has to be alligned here. If not, we will have to fix it.
    masm.checkStackAlignment();

    // Push registers such that we can access them from [base + code].
    masm.PushRegsInMask(AllRegs);

    // Pass pointer to InvalidationBailoutStack structure.
    masm.movePtr(StackPointer, r3);

    // Reserve place for return value and BailoutInfo pointer
    masm.subPtr(Imm32(2 * sizeof(uintptr_t)), StackPointer);
    // Pass pointer to return value.
    masm.as_addi(r4, StackPointer, (uint16_t)sizeof(uintptr_t));
    // Pass pointer to BailoutInfo
    masm.movePtr(StackPointer, r5);

    masm.setupAlignedABICall();
    masm.passABIArg(r3);
    masm.passABIArg(r4);
    masm.passABIArg(r5);
    masm.callWithABI(JS_FUNC_TO_DATA_PTR(void*, InvalidationBailout), MoveOp::GENERAL,
                     CheckUnsafeCallWithABI::DontCheckOther);

    masm.loadPtr(Address(StackPointer, 0), r5);
    masm.loadPtr(Address(StackPointer, sizeof(uintptr_t)), r4);
    // Remove the return address, the IonScript, the register state
    // (InvaliationBailoutStack) and the space that was allocated for the
    // return value.
    masm.addPtr(Imm32(sizeof(InvalidationBailoutStack) + 2 * sizeof(uintptr_t)), StackPointer);
    // Remove the space that this frame was using before the bailout
    // (computed by InvalidationBailout).
    masm.addPtr(r4, StackPointer);

    // Jump to shared bailout tail. The BailoutInfo pointer remains in r5.
    // The return code is left unchanged by this routine in r3.
    masm.jump(bailoutTail);
}

void
JitRuntime::generateArgumentsRectifier(MacroAssembler& masm)
{
    ADBlock("generateArgumentsRectifier");
    // Do not erase the frame pointer in this function.

    // MIPS uses a5-a7, t0-t3 and s3, with s3 being the only callee-save register.
    // We will do something similar for Power and use r4-r6, r7-r10 and r15.
    const Register nvRectReg = r15;

    argumentsRectifierOffset_ = startTrampolineCode(masm);
    masm.pushReturnAddress();
    // Caller:
    // [arg2] [arg1] [this] [[argc] [callee] [descr] [raddr]] <- sp

    // Add |this|, in the counter of known arguments.
    masm.loadPtr(Address(StackPointer, RectifierFrameLayout::offsetOfNumActualArgs()), nvRectReg);
    masm.addPtr(Imm32(1), nvRectReg);

    const Register numActArgsReg = r5;
    const Register calleeTokenReg = r6;
    const Register tempValue = r7;
    const Register numArgsReg = r4;
    const Register numToPush = r8;
    const Register tempCalleeTokenReg = r9;
    const Register tempNumArgsReg = r10;

    // Load |nformals| into numArgsReg.
    masm.loadPtr(Address(StackPointer, RectifierFrameLayout::offsetOfCalleeToken()),
                 calleeTokenReg);
    masm.mov(calleeTokenReg, numArgsReg);
    masm.andPtr(Imm32(uint32_t(CalleeTokenMask)), numArgsReg);
    masm.load16ZeroExtend(Address(numArgsReg, JSFunction::offsetOfNargs()), numArgsReg);

    // Stash another copy since we're going to clobber numArgsReg.
    masm.as_or(tempNumArgsReg, numArgsReg, numArgsReg);

    static_assert(CalleeToken_FunctionConstructing == 1,
      "Ensure that we can use the constructing bit to count the value");
    masm.mov(calleeTokenReg, tempCalleeTokenReg);
    masm.ma_and(tempCalleeTokenReg, Imm32(uint32_t(CalleeToken_FunctionConstructing)));

    // Including |this|, and |new.target|, there are (|nformals| + 1 + isConstructing)
    // arguments to push to the stack.  Then we push a JitFrameLayout.  We
    // compute the padding expressed in the number of extra |undefined| values
    // to push on the stack.
    static_assert(sizeof(JitFrameLayout) % JitStackAlignment == 0,
      "No need to consider the JitFrameLayout for aligning the stack");
    static_assert(JitStackAlignment % sizeof(Value) == 0,
      "Ensure that we can pad the stack by pushing extra UndefinedValue");

    MOZ_ASSERT(mozilla::IsPowerOfTwo(JitStackValueAlignment));
    masm.add32(Imm32(JitStackValueAlignment - 1 /* for padding */ + 1 /* for |this| */), numArgsReg);
    masm.add32(tempCalleeTokenReg, numArgsReg);
    masm.and32(Imm32(~(JitStackValueAlignment - 1)), numArgsReg);

    // Load the number of |undefined|s to push (nargs - nvRectReg).
    masm.as_subf(numToPush, nvRectReg, numArgsReg); // T = B - A

    // Caller:
    // [arg2] [arg1] [this] [[argc] [callee] [descr] [raddr]] <- sp <- r9
    // '--- nvRectReg ---'
    //
    // Rectifier frame:
    // [undef] [undef] [undef] [arg2] [arg1] [this] [[argc] [callee] [descr] [raddr]]
    // '-------- r8 ---------' '---- nvRectReg ---'

    // Copy number of actual arguments into numActArgsReg
    masm.loadPtr(Address(StackPointer, RectifierFrameLayout::offsetOfNumActualArgs()),
                 numActArgsReg);


    masm.moveValue(UndefinedValue(), ValueOperand(tempValue));

    masm.movePtr(StackPointer, tempCalleeTokenReg); // Save stack pointer. We can clobber it.

    // Push undefined (including the padding).
    {
        Label undefLoopTop;

        masm.bind(&undefLoopTop);
        masm.sub32(Imm32(1), numToPush);
        masm.subPtr(Imm32(sizeof(Value)), StackPointer);
        masm.storeValue(ValueOperand(tempValue), Address(StackPointer, 0));

        masm.ma_b(numToPush, numToPush, &undefLoopTop, Assembler::NonZero, ShortJump);
    }

    // Get the topmost argument.
    static_assert(sizeof(Value) == 8, "TimesEight is used to skip arguments");

    // | - sizeof(Value)| is used to put rcx such that we can read the last
    // argument, and not the value which is after.
    MOZ_ASSERT(tempValue == r7); // can clobber
    MOZ_ASSERT(numToPush == r8);
    MOZ_ASSERT(tempCalleeTokenReg == r9); // can clobber
    masm.xs_slwi(r7, nvRectReg, 3); // r7 <- nargs * 8
    masm.as_add(numToPush, r9, r7); // r8 <- t9(saved sp) + nargs * 8
    masm.addPtr(Imm32(sizeof(RectifierFrameLayout) - sizeof(Value)), numToPush);

    // Copy and push arguments |nargs| + 1 times (to include |this|).
    {
        Label copyLoopTop;

        masm.bind(&copyLoopTop);
        masm.sub32(Imm32(1), nvRectReg);
        masm.subPtr(Imm32(sizeof(Value)), StackPointer);
        masm.loadValue(Address(numToPush, 0), ValueOperand(tempValue));
        masm.storeValue(ValueOperand(tempValue), Address(StackPointer, 0));
        masm.subPtr(Imm32(sizeof(Value)), numToPush);

        masm.ma_b(nvRectReg, nvRectReg, &copyLoopTop, Assembler::NonZero, ShortJump);
    }

    // If constructing, copy newTarget also.
    {
        Label notConstructing;

        masm.branchTest32(Assembler::Zero, calleeTokenReg, Imm32(CalleeToken_FunctionConstructing),
                          &notConstructing);

        // thisFrame[numFormals] = prevFrame[argc]
        ValueOperand newTarget(tempValue);

        // +1 for |this|. We want vp[argc], so don't subtract 1.
        BaseIndex newTargetSrc(r9, numActArgsReg, TimesEight, sizeof(RectifierFrameLayout) + sizeof(Value));
        masm.loadValue(newTargetSrc, newTarget);

        // Again, 1 for |this|. We bring back our saved register from above.
        BaseIndex newTargetDest(StackPointer, tempNumArgsReg, TimesEight, sizeof(Value));
        masm.storeValue(newTarget, newTargetDest);

        masm.bind(&notConstructing);
    }

    // Caller:
    // [arg2] [arg1] [this] [[argc] [callee] [descr] [raddr]] <- r9
    //
    //
    // Rectifier frame:
    // [undef] [undef] [undef] [arg2] [arg1] [this] <- sp [[argc] [callee] [descr] [raddr]]

    MOZ_ASSERT(numToPush == r8); // can clobber
    MOZ_ASSERT(tempCalleeTokenReg == r9); // can clobber

    // Construct sizeDescriptor.
    masm.subPtr(StackPointer, r9);
    masm.makeFrameDescriptor(r9, JitFrame_Rectifier, JitFrameLayout::Size());

    // Construct JitFrameLayout.
    masm.subPtr(Imm32(3 * sizeof(uintptr_t)), StackPointer);
    // Push actual arguments.
    masm.storePtr(numActArgsReg, Address(StackPointer, 2 * sizeof(uintptr_t)));
    // Push callee token.
    masm.storePtr(calleeTokenReg, Address(StackPointer, sizeof(uintptr_t)));
    // Push frame descriptor.
    masm.storePtr(r9, Address(StackPointer, 0));

    // Call the target function.
    masm.andPtr(Imm32(uint32_t(CalleeTokenMask)), calleeTokenReg);
    masm.loadJitCodeRaw(calleeTokenReg, r8);
    argumentsRectifierReturnOffset_ = masm.callJitNoProfiler(t1);

    // Remove the rectifier frame.
    masm.loadPtr(Address(StackPointer, 0), r9);
    masm.rshiftPtr(Imm32(FRAMESIZE_SHIFT), r9);

    // Discard descriptor, calleeToken and number of actual arguments.
    masm.addPtr(Imm32(3 * sizeof(uintptr_t)), StackPointer);

    // Discard pushed arguments.
    masm.addPtr(r9, StackPointer);

    masm.ret();
}

/* - When bailout is done via out of line code (lazy bailout).
 * Frame size is stored in LR (look at
 * CodeGeneratorPPC64LE::generateOutOfLineCode()) and thunk code should save it
 * on stack. In addition, snapshotOffset_ and padding_ are
 * pushed to the stack by CodeGeneratorPPC64LE::visitOutOfLineBailout(). Field
 * frameClassId_ is forced to be NO_FRAME_SIZE_CLASS_ID
 * (see JitRuntime::generateBailoutHandler).
 */
static void
PushBailoutFrame(MacroAssembler& masm, Register spArg)
{
    // Push the frameSize_ stored in LR.
    masm.xs_mflr(ScratchRegister);
    masm.push(ScratchRegister);

    // Push registers such that we can access them from [base + code].
    masm.PushRegsInMask(AllRegs);

    // Put pointer to BailoutStack as first argument to the Bailout().
    masm.movePtr(StackPointer, spArg);
}

static void
GenerateBailoutThunk(MacroAssembler& masm, uint32_t frameClass, Label* bailoutTail)
{
    PushBailoutFrame(masm, r3);

    // Put pointer to BailoutInfo.
    static const uint32_t sizeOfBailoutInfo = sizeof(uintptr_t) * 2;
    masm.subPtr(Imm32(sizeOfBailoutInfo), StackPointer);
    masm.movePtr(StackPointer, r4);

    masm.setupAlignedABICall();
    masm.passABIArg(r3);
    masm.passABIArg(r4);
    masm.callWithABI(JS_FUNC_TO_DATA_PTR(void*, Bailout), MoveOp::GENERAL,
                     CheckUnsafeCallWithABI::DontCheckOther);

    // Get BailoutInfo pointer.
    masm.loadPtr(Address(StackPointer, 0), r5);

    // Stack is:
    //     [frame]
    //     snapshotOffset
    //     frameSize
    //     [bailoutFrame]
    //     [bailoutInfo]
    //
    // Remove both the bailout frame and the topmost Ion frame's stack.
    // First, load frameSize from stack.
    masm.loadPtr(Address(StackPointer,
                         sizeOfBailoutInfo + BailoutStack::offsetOfFrameSize()), r4);
    // Remove complete BailoutStack class and data after it.
    masm.addPtr(Imm32(sizeof(BailoutStack) + sizeOfBailoutInfo), StackPointer);
    // Finally, remove frame size from stack.
    masm.addPtr(r4, StackPointer);

    // Jump to shared bailout tail. The BailoutInfo pointer is still in r5 and
    // the return code is already in r3, so we can just branch.
    masm.jump(bailoutTail);
}

JitRuntime::BailoutTable
JitRuntime::generateBailoutTable(MacroAssembler& masm, Label* bailoutTail, uint32_t frameClass)
{
    MOZ_CRASH("PPC64LE does not use bailout tables");
}

void
JitRuntime::generateBailoutHandler(MacroAssembler& masm, Label* bailoutTail)
{
    ADBlock("generateBailoutHandler");
    bailoutHandlerOffset_ = startTrampolineCode(masm);

    GenerateBailoutThunk(masm, NO_FRAME_SIZE_CLASS_ID, bailoutTail);
}

bool
JitRuntime::generateVMWrapper(JSContext* cx, MacroAssembler& masm, const VMFunction& f)
{
    ADBlock("generateVMWrapper");
    MOZ_ASSERT(functionWrappers_);
    MOZ_ASSERT(functionWrappers_->initialized());

    uint32_t wrapperOffset = startTrampolineCode(masm);

    AllocatableGeneralRegisterSet regs(Register::Codes::WrapperMask);

    static_assert((Register::Codes::VolatileMask & ~Register::Codes::WrapperMask) == 0,
                  "Wrapper register set should be a superset of Volatile register set.");

    // The context is the first argument; a0 is the first argument register.
    Register cxreg = r3;
    regs.take(cxreg);

    // If it isn't a tail call, then the return address needs to be saved.
    if (f.expectTailCall == NonTailCall)
        masm.pushReturnAddress();

    // We're aligned to an exit frame, so link it up.
    masm.loadJSContext(cxreg);
    masm.enterExitFrame(cxreg, regs.getAny(), &f);

    // Save the base of the argument set stored on the stack.
    Register argsBase = InvalidReg;
    if (f.explicitArgs) {
        argsBase = t1; // Use temporary register.
        regs.take(argsBase);
        masm.as_addi(argsBase, StackPointer, ExitFrameLayout::SizeWithFooter());
    }

    // Reserve space for the outparameter.
    Register outReg = InvalidReg;
    switch (f.outParam) {
      case Type_Value:
        outReg = regs.takeAny();
        masm.reserveStack(sizeof(Value));
        masm.movePtr(StackPointer, outReg);
        break;

      case Type_Handle:
        outReg = regs.takeAny();
        masm.PushEmptyRooted(f.outParamRootType);
        masm.movePtr(StackPointer, outReg);
        break;

      case Type_Bool:
      case Type_Int32:
        outReg = regs.takeAny();
        // Reserve 4-byte space to make stack aligned to 8-byte.
        masm.reserveStack(2 * sizeof(int32_t));
        masm.movePtr(StackPointer, outReg);
        break;

      case Type_Pointer:
        outReg = regs.takeAny();
        masm.reserveStack(sizeof(uintptr_t));
        masm.movePtr(StackPointer, outReg);
        break;

      case Type_Double:
        outReg = regs.takeAny();
        masm.reserveStack(sizeof(double));
        masm.movePtr(StackPointer, outReg);
        break;

      default:
        MOZ_ASSERT(f.outParam == Type_Void);
        break;
    }

    if (!generateTLEnterVM(masm, f))
        return false;

    masm.setupUnalignedABICall(regs.getAny());
    masm.passABIArg(cxreg);

    size_t argDisp = 0;

    // Copy any arguments.
    for (uint32_t explicitArg = 0; explicitArg < f.explicitArgs; explicitArg++) {
        MoveOperand from;
        switch (f.argProperties(explicitArg)) {
          case VMFunction::WordByValue:
            if (f.argPassedInFloatReg(explicitArg))
                masm.passABIArg(MoveOperand(argsBase, argDisp), MoveOp::DOUBLE);
            else
                masm.passABIArg(MoveOperand(argsBase, argDisp), MoveOp::GENERAL);
            argDisp += sizeof(void*);
            break;
          case VMFunction::WordByRef:
            masm.passABIArg(MoveOperand(argsBase, argDisp, MoveOperand::EFFECTIVE_ADDRESS),
                            MoveOp::GENERAL);
            argDisp += sizeof(void*);
            break;
          case VMFunction::DoubleByValue:
          case VMFunction::DoubleByRef:
            MOZ_CRASH("NYI: PPC64 callVM no support for 128-bit values");
            break;
        }
    }

    // Copy the implicit outparam, if any.
    if (InvalidReg != outReg)
        masm.passABIArg(outReg);

    masm.callWithABI(f.wrapped, MoveOp::GENERAL, CheckUnsafeCallWithABI::DontCheckHasExitFrame);

    if (!generateTLExitVM(masm, f))
        return false;

    // Test for failure.
    switch (f.failType()) {
      case Type_Object:
        masm.branchTestPtr(Assembler::Zero, r3, r3, masm.failureLabel());
        break;
      case Type_Bool:
        // Called functions return bools, which are 0/false and non-zero/true.
        masm.branchIfFalseBool(r3, masm.failureLabel());
        break;
      case Type_Void:
        break;
      default:
        MOZ_CRASH("unknown failure kind");
    }

    // Load the outparam and free any allocated stack.
    switch (f.outParam) {
      case Type_Handle:
        masm.popRooted(f.outParamRootType, ReturnReg, JSReturnOperand);
        break;

      case Type_Value:
        masm.loadValue(Address(StackPointer, 0), JSReturnOperand);
        masm.freeStack(sizeof(Value));
        break;

      case Type_Int32:
        masm.load32(Address(StackPointer, 0), ReturnReg);
        masm.freeStack(2 * sizeof(int32_t));
        break;

      case Type_Pointer:
        masm.loadPtr(Address(StackPointer, 0), ReturnReg);
        masm.freeStack(sizeof(uintptr_t));
        break;

      case Type_Bool:
        // Boolean on Power ISA is not natively a byte.
        masm.load32(StackPointer, 0), ReturnReg);
        masm.freeStack(2 * sizeof(int32_t));
        break;

      case Type_Double:
        masm.loadDouble(Address(StackPointer, 0), ReturnDoubleReg);
        masm.freeStack(sizeof(double));
        break;

      default:
        MOZ_ASSERT(f.outParam == Type_Void);
        break;
    }

    masm.leaveExitFrame();
    masm.retn(Imm32(sizeof(ExitFrameLayout) +
                    f.explicitStackSlots() * sizeof(void*) +
                    f.extraValuesToPop * sizeof(Value)));

    return functionWrappers_->putNew(&f, wrapperOffset);
}

uint32_t
JitRuntime::generatePreBarrier(JSContext* cx, MacroAssembler& masm, MIRType type)
{
    ADBlock("generatePreBarrier");
    uint32_t offset = startTrampolineCode(masm);

    MOZ_ASSERT(PreBarrierReg == r4);
    Register temp1 = r3;
    Register temp2 = r5;
    Register temp3 = r6;
    masm.push(temp1);
    masm.push(temp2);
    masm.push(temp3);

    Label noBarrier;
    masm.emitPreBarrierFastPath(cx->runtime(), type, temp1, temp2, temp3, &noBarrier);

    // Call into C++ to mark this GC thing.
    masm.pop(temp3);
    masm.pop(temp2);
    masm.pop(temp1);

    // Explicitly save LR, since we can't use it in PushRegsInMask.
    masm.xs_mflr(ScratchRegister);
    LiveRegisterSet save;
    save.set() = RegisterSet(GeneralRegisterSet(Registers::VolatileMask),
                             FloatRegisterSet(FloatRegisters::VolatileMask));
    masm.PushRegsInMask(save);

    masm.movePtr(ImmPtr(cx->runtime()), r3);

    masm.setupUnalignedABICall(r5);
    masm.passABIArg(r3);
    masm.passABIArg(r4);
    masm.callWithABI(JitMarkFunction(type));

    masm.PopRegsInMask(save);
    // Explicitly restore LR.
    masm.xs_mtlr(ScratchRegister);
    masm.ret();

    masm.bind(&noBarrier);
    masm.pop(temp3);
    masm.pop(temp2);
    masm.pop(temp1);
    masm.abiret();

    return offset;
}

typedef bool (*HandleDebugTrapFn)(JSContext*, BaselineFrame*, uint8_t*, bool*);
static const VMFunction HandleDebugTrapInfo =
    FunctionInfo<HandleDebugTrapFn>(HandleDebugTrap, "HandleDebugTrap");

JitCode*
JitRuntime::generateDebugTrapHandler(JSContext* cx)
{
    ADBlock("generateDebugTrapHandler");
    StackMacroAssembler masm(cx);

    Register scratch1 = r6;
    Register scratch2 = r5;
    Register scratch3 = r15; // non-volatile

    // Load BaselineFrame pointer in scratch1.
    masm.movePtr(scratch3, scratch1);
    masm.subPtr(Imm32(BaselineFrame::Size()), scratch1);

    // Enter a stub frame and call the HandleDebugTrap VM function. Ensure
    // the stub frame has a nullptr ICStub pointer, since this pointer is
    // marked during GC.
    masm.movePtr(ImmPtr(nullptr), ICStubReg);
    EmitBaselineEnterStubFrame(masm, scratch2);

    TrampolinePtr code = cx->runtime()->jitRuntime()->getVMWrapper(HandleDebugTrapInfo);

    masm.subPtr(Imm32(2 * sizeof(uintptr_t)), StackPointer);
    // Save return address.
    masm.xs_mflr(ScratchReg);
    masm.storePtr(ScratchReg, Address(StackPointer, sizeof(uintptr_t)));
    masm.storePtr(scratch1, Address(StackPointer, 0));

    EmitBaselineCallVM(code, masm);

    EmitBaselineLeaveStubFrame(masm);

    // If the stub returns |true|, we have to perform a forced return
    // (return from the JS frame). If the stub returns |false|, just return
    // from the trap stub so that execution continues at the current pc.
    Label forcedReturn;
    masm.branchTest32(Assembler::NonZero, ReturnReg, ReturnReg, &forcedReturn);

    // LR was restored by EmitLeaveStubFrame. It may have changed.
    masm.as_blr();

    masm.bind(&forcedReturn);
    masm.loadValue(Address(scratch3, BaselineFrame::reverseOffsetOfReturnValue()),
                   JSReturnOperand);
    masm.movePtr(scratch3, StackPointer);
    masm.pop(scratch3);

    // Before returning, if profiling is turned on, make sure that lastProfilingFrame
    // is set to the correct caller frame.
    {
        Label skipProfilingInstrumentation;
        AbsoluteAddress addressOfEnabled(cx->runtime()->geckoProfiler().addressOfEnabled());
        masm.branch32(Assembler::Equal, addressOfEnabled, Imm32(0), &skipProfilingInstrumentation);
        masm.profilerExitFrame();
        masm.bind(&skipProfilingInstrumentation);
    }

    masm.ret();

    Linker linker(masm);
    AutoFlushICache afc("DebugTrapHandler");
    JitCode* codeDbg = linker.newCode(cx, CodeKind::Other);

#ifdef JS_ION_PERF
    writePerfSpewerJitCodeProfile(codeDbg, "DebugTrapHandler");
#endif

    return codeDbg;
}

void
JitRuntime::generateExceptionTailStub(MacroAssembler& masm, void* handler, Label* profilerExitTail)
{
    ADBlock("generateExceptionTailStub");
    exceptionTailOffset_ = startTrampolineCode(masm);

    masm.bind(masm.failureLabel());
    masm.handleFailureWithHandlerTail(handler, profilerExitTail);
}

void
JitRuntime::generateBailoutTailStub(MacroAssembler& masm, Label* bailoutTail)
{
    ADBlock("generateBailoutTailStub");
    bailoutTailOffset_ = startTrampolineCode(masm);
    masm.bind(bailoutTail);

    masm.generateBailoutTail(r4, r5);
}

void
JitRuntime::generateProfilerExitFrameTailStub(MacroAssembler& masm, Label* profilerExitTail)
{
    ADBlock("generateProfilerExitFrameTailStub");
    profilerExitFrameTailOffset_ = startTrampolineCode(masm);
    masm.bind(profilerExitTail);

    Register scratch1 = r7; // XXX?
    Register scratch2 = r8;
    Register scratch3 = r9;
    Register scratch4 = r10;

    //
    // The code generated below expects that the current stack pointer points
    // to an Ion or Baseline frame, at the state it would be immediately
    // before a ret().  Thus, after this stub's business is done, it executes
    // a ret() and returns directly to the caller script, on behalf of the
    // callee script that jumped to this code.
    //
    // Thus the expected stack is:
    //
    //                                   StackPointer ----+
    //                                                    v
    // ..., ActualArgc, CalleeToken, Descriptor, ReturnAddr
    // MEM-HI                                       MEM-LOW
    //
    //
    // The generated jitcode is responsible for overwriting the
    // jitActivation->lastProfilingFrame field with a pointer to the previous
    // Ion or Baseline jit-frame that was pushed before this one. It is also
    // responsible for overwriting jitActivation->lastProfilingCallSite with
    // the return address into that frame.  The frame could either be an
    // immediate "caller" frame, or it could be a frame in a previous
    // JitActivation (if the current frame was entered from C++, and the C++
    // was entered by some caller jit-frame further down the stack).
    //
    // So this jitcode is responsible for "walking up" the jit stack, finding
    // the previous Ion or Baseline JS frame, and storing its address and the
    // return address into the appropriate fields on the current jitActivation.
    //
    // There are a fixed number of different path types that can lead to the
    // current frame, which is either a baseline or ion frame:
    //
    // <Baseline-Or-Ion>
    // ^
    // |
    // ^--- Ion
    // |
    // ^--- Baseline Stub <---- Baseline
    // |
    // ^--- Argument Rectifier
    // |    ^
    // |    |
    // |    ^--- Ion
    // |    |
    // |    ^--- Baseline Stub <---- Baseline
    // |
    // ^--- Entry Frame (From C++)
    //
    Register actReg = scratch4;
    masm.loadJSContext(actReg);
    masm.loadPtr(Address(actReg, offsetof(JSContext, profilingActivation_)), actReg);

    Address lastProfilingFrame(actReg, JitActivation::offsetOfLastProfilingFrame());
    Address lastProfilingCallSite(actReg, JitActivation::offsetOfLastProfilingCallSite());

#ifdef DEBUG
    // Ensure that frame we are exiting is current lastProfilingFrame
    {
        masm.loadPtr(lastProfilingFrame, scratch1);
        Label checkOk;
        masm.branchPtr(Assembler::Equal, scratch1, ImmWord(0), &checkOk);
        masm.branchPtr(Assembler::Equal, StackPointer, scratch1, &checkOk);
        masm.assumeUnreachable(
            "Mismatch between stored lastProfilingFrame and current stack pointer.");
        masm.bind(&checkOk);
    }
#endif

    // Load the frame descriptor into |scratch1|, figure out what to do depending on its type.
    masm.loadPtr(Address(StackPointer, JitFrameLayout::offsetOfDescriptor()), scratch1);

    // Going into the conditionals, we will have:
    //      FrameDescriptor.size in scratch1
    //      FrameDescriptor.type in scratch2
    masm.ma_and(scratch2, scratch1, Imm32((1 << FRAMETYPE_BITS) - 1));
    masm.rshiftPtr(Imm32(FRAMESIZE_SHIFT), scratch1);

    // Handling of each case is dependent on FrameDescriptor.type
    Label handle_IonJS;
    Label handle_BaselineStub;
    Label handle_Rectifier;
    Label handle_IonICCall;
    Label handle_Entry;
    Label end;

    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_IonJS), &handle_IonJS);
    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_BaselineJS), &handle_IonJS);
    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_BaselineStub), &handle_BaselineStub);
    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_Rectifier), &handle_Rectifier);
    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_IonICCall), &handle_IonICCall);
    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_CppToJSJit), &handle_Entry);

    // The WasmToJSJit is just another kind of entry.
    masm.branch32(Assembler::Equal, scratch2, Imm32(JitFrame_WasmToJSJit), &handle_Entry);

    masm.assumeUnreachable("Invalid caller frame type when exiting from Ion frame.");

    //
    // JitFrame_IonJS
    //
    // Stack layout:
    //                  ...
    //                  Ion-Descriptor
    //     Prev-FP ---> Ion-ReturnAddr
    //                  ... previous frame data ... |- Descriptor.Size
    //                  ... arguments ...           |
    //                  ActualArgc          |
    //                  CalleeToken         |- JitFrameLayout::Size()
    //                  Descriptor          |
    //        FP -----> ReturnAddr          |
    //
    masm.bind(&handle_IonJS);
    {
        // |scratch1| contains Descriptor.size

        // returning directly to an IonJS frame.  Store return addr to frame
        // in lastProfilingCallSite.
        masm.loadPtr(Address(StackPointer, JitFrameLayout::offsetOfReturnAddress()), scratch2);
        masm.storePtr(scratch2, lastProfilingCallSite);

        // Store return frame in lastProfilingFrame.
        // scratch2 := StackPointer + Descriptor.size*1 + JitFrameLayout::Size();
        masm.as_add(scratch2, StackPointer, scratch1);
        masm.as_addi(scratch2, scratch2, JitFrameLayout::Size());
        masm.storePtr(scratch2, lastProfilingFrame);
        masm.ret();
    }

    //
    // JitFrame_BaselineStub
    //
    // Look past the stub and store the frame pointer to
    // the baselineJS frame prior to it.
    //
    // Stack layout:
    //              ...
    //              BL-Descriptor
    // Prev-FP ---> BL-ReturnAddr
    //      +-----> BL-PrevFramePointer
    //      |       ... BL-FrameData ...
    //      |       BLStub-Descriptor
    //      |       BLStub-ReturnAddr
    //      |       BLStub-StubPointer          |
    //      +------ BLStub-SavedFramePointer    |- Descriptor.Size
    //              ... arguments ...           |
    //              ActualArgc          |
    //              CalleeToken         |- JitFrameLayout::Size()
    //              Descriptor          |
    //    FP -----> ReturnAddr          |
    //
    // We take advantage of the fact that the stub frame saves the frame
    // pointer pointing to the baseline frame, so a bunch of calculation can
    // be avoided.
    //
    masm.bind(&handle_BaselineStub);
    {
        masm.as_add(scratch3, StackPointer, scratch1);
        Address stubFrameReturnAddr(scratch3,
                                    JitFrameLayout::Size() +
                                    BaselineStubFrameLayout::offsetOfReturnAddress());
        masm.loadPtr(stubFrameReturnAddr, scratch2);
        masm.storePtr(scratch2, lastProfilingCallSite);

        Address stubFrameSavedFramePtr(scratch3,
                                       JitFrameLayout::Size() - (2 * sizeof(void*)));
        masm.loadPtr(stubFrameSavedFramePtr, scratch2);
        masm.addPtr(Imm32(sizeof(void*)), scratch2); // Skip past BL-PrevFramePtr
        masm.storePtr(scratch2, lastProfilingFrame);
        masm.ret();
    }


    //
    // JitFrame_Rectifier
    //
    // The rectifier frame can be preceded by either an IonJS, a BaselineStub,
    // or a CppToJSJit/WasmToJSJit frame.
    //
    // Stack layout if caller of rectifier was Ion or CppToJSJit/WasmToJSJit:
    //
    //              Ion-Descriptor
    //              Ion-ReturnAddr
    //              ... ion frame data ... |- Rect-Descriptor.Size
    //              < COMMON LAYOUT >
    //
    // Stack layout if caller of rectifier was Baseline:
    //
    //              BL-Descriptor
    // Prev-FP ---> BL-ReturnAddr
    //      +-----> BL-SavedFramePointer
    //      |       ... baseline frame data ...
    //      |       BLStub-Descriptor
    //      |       BLStub-ReturnAddr
    //      |       BLStub-StubPointer          |
    //      +------ BLStub-SavedFramePointer    |- Rect-Descriptor.Size
    //              ... args to rectifier ...   |
    //              < COMMON LAYOUT >
    //
    // Common stack layout:
    //
    //              ActualArgc          |
    //              CalleeToken         |- IonRectitiferFrameLayout::Size()
    //              Rect-Descriptor     |
    //              Rect-ReturnAddr     |
    //              ... rectifier data & args ... |- Descriptor.Size
    //              ActualArgc      |
    //              CalleeToken     |- JitFrameLayout::Size()
    //              Descriptor      |
    //    FP -----> ReturnAddr      |
    //
    masm.bind(&handle_Rectifier);
    {
        // scratch2 := StackPointer + Descriptor.size*1 + JitFrameLayout::Size();
        masm.as_add(scratch2, StackPointer, scratch1);
        masm.addPtr(Imm32(JitFrameLayout::Size()), scratch2);
        masm.loadPtr(Address(scratch2, RectifierFrameLayout::offsetOfDescriptor()), scratch3);
        masm.xs_srwi(scratch1, scratch3, FRAMESIZE_SHIFT);
        masm.and32(Imm32((1 << FRAMETYPE_BITS) - 1), scratch3);

        // Now |scratch1| contains Rect-Descriptor.Size
        // and |scratch2| points to Rectifier frame
        // and |scratch3| contains Rect-Descriptor.Type

        masm.assertRectifierFrameParentType(scratch3);

        // Check for either Ion or BaselineStub frame.
        Label notIonFrame;
        masm.branch32(Assembler::NotEqual, scratch3, Imm32(JitFrame_IonJS), &notIonFrame);

        // Handle Rectifier <- IonJS
        // scratch3 := RectFrame[ReturnAddr]
        masm.loadPtr(Address(scratch2, RectifierFrameLayout::offsetOfReturnAddress()), scratch3);
        masm.storePtr(scratch3, lastProfilingCallSite);

        // scratch3 := RectFrame + Rect-Descriptor.Size + RectifierFrameLayout::Size()
        masm.as_add(scratch3, scratch2, scratch1);
        masm.addPtr(Imm32(RectifierFrameLayout::Size()), scratch3);
        masm.storePtr(scratch3, lastProfilingFrame);
        masm.ret();

        masm.bind(&notIonFrame);

        // Check for either BaselineStub or a CppToJSJit/WasmToJSJit entry
        // frame.
        masm.branch32(Assembler::NotEqual, scratch3, Imm32(JitFrame_BaselineStub), &handle_Entry);

        // Handle Rectifier <- BaselineStub <- BaselineJS
        masm.as_add(scratch3, scratch2, scratch1);
        Address stubFrameReturnAddr(scratch3, RectifierFrameLayout::Size() +
                                              BaselineStubFrameLayout::offsetOfReturnAddress());
        masm.loadPtr(stubFrameReturnAddr, scratch2);
        masm.storePtr(scratch2, lastProfilingCallSite);

        Address stubFrameSavedFramePtr(scratch3,
                                       RectifierFrameLayout::Size() - (2 * sizeof(void*)));
        masm.loadPtr(stubFrameSavedFramePtr, scratch2);
        masm.addPtr(Imm32(sizeof(void*)), scratch2);
        masm.storePtr(scratch2, lastProfilingFrame);
        masm.ret();
    }

    // JitFrame_IonICCall
    //
    // The caller is always an IonJS frame.
    //
    //              Ion-Descriptor
    //              Ion-ReturnAddr
    //              ... ion frame data ... |- CallFrame-Descriptor.Size
    //              StubCode               |
    //              ICCallFrame-Descriptor |- IonICCallFrameLayout::Size()
    //              ICCallFrame-ReturnAddr |
    //              ... call frame data & args ... |- Descriptor.Size
    //              ActualArgc      |
    //              CalleeToken     |- JitFrameLayout::Size()
    //              Descriptor      |
    //    FP -----> ReturnAddr      |
    masm.bind(&handle_IonICCall);
    {
        // scratch2 := StackPointer + Descriptor.size + JitFrameLayout::Size()
        masm.as_add(scratch2, StackPointer, scratch1);
        masm.addPtr(Imm32(JitFrameLayout::Size()), scratch2);

        // scratch3 := ICCallFrame-Descriptor.Size
        masm.loadPtr(Address(scratch2, IonICCallFrameLayout::offsetOfDescriptor()), scratch3);
#ifdef DEBUG
        // Assert previous frame is an IonJS frame.
        masm.movePtr(scratch3, scratch1);
        masm.and32(Imm32((1 << FRAMETYPE_BITS) - 1), scratch1);
        {
            Label checkOk;
            masm.branch32(Assembler::Equal, scratch1, Imm32(JitFrame_IonJS), &checkOk);
            masm.assumeUnreachable("IonICCall frame must be preceded by IonJS frame");
            masm.bind(&checkOk);
        }
#endif
        masm.rshiftPtr(Imm32(FRAMESIZE_SHIFT), scratch3);

        // lastProfilingCallSite := ICCallFrame-ReturnAddr
        masm.loadPtr(Address(scratch2, IonICCallFrameLayout::offsetOfReturnAddress()), scratch1);
        masm.storePtr(scratch1, lastProfilingCallSite);

        // lastProfilingFrame := ICCallFrame + ICCallFrame-Descriptor.Size +
        //                       IonICCallFrameLayout::Size()
        masm.as_add(scratch1, scratch2, scratch3);
        masm.addPtr(Imm32(IonICCallFrameLayout::Size()), scratch1);
        masm.storePtr(scratch1, lastProfilingFrame);
        masm.ret();
    }

    //
    // JitFrame_CppToJSJit / JitFrame_WasmToJSJit
    //
    // If at an entry frame, store null into both fields.
    // A fast-path wasm->jit transition frame is an entry frame from the point
    // of view of the JIT.
    //
    masm.bind(&handle_Entry);
    {
        masm.movePtr(ImmPtr(nullptr), scratch1);
        masm.storePtr(scratch1, lastProfilingCallSite);
        masm.storePtr(scratch1, lastProfilingFrame);
        masm.ret();
    }
}
