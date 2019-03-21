/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#ifndef jit_ppc64le_SharedICRegisters_ppc64le_h
#define jit_ppc64le_SharedICRegisters_ppc64le_h

#include "jit/MacroAssembler.h"

namespace js {
namespace jit {

// The frame register should be allocatable but non-volatile.
static constexpr Register BaselineFrameReg = r13;
// This is just an alias for the stack pointer currently.
static constexpr Register BaselineStackReg = r1;

// ValueOperands R0, R1, and R2.
// R0 == JSReturnReg, and R2 uses registers not preserved across calls. R1 value
// should be preserved across calls.
static constexpr ValueOperand R0(r4);
static constexpr ValueOperand R1(r15); // non-volatile
static constexpr ValueOperand R2(r5);

// ICTailCallReg and ICStubReg
// These use registers that are not preserved across calls.
// The tail call register situation is rather weird on Power: LR is an SPR, not
// a GPR. We have to do some manual patching in the JIT to deal with this issue
// since it assumes it can just use the tail call register like any other
// register. The invalid value is just a dummy to put something here.
#error fix JIT to deal with ICTailCallReg in jit and shared
static constexpr Register ICTailCallReg = InvalidReg;
static constexpr Register ICStubReg = r7;

static constexpr Register ExtractTemp0 = InvalidReg;
static constexpr Register ExtractTemp1 = InvalidReg;

// Register used internally by the Power Macro Assembler.
static constexpr Register BaselineSecondScratchReg = SecondScratchReg;

// FloatReg0 must be equal to ReturnFloatReg.
static constexpr FloatRegister FloatReg0 = f1;
static constexpr FloatRegister FloatReg1 = f2;

} // namespace jit
} // namespace js

#endif /* jit_ppc64le_SharedICRegisters_ppc64le_h */
