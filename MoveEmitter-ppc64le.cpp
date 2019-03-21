/* -*- Mode: C++; tab-width: 8; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * vim: set ts=8 sts=4 et sw=4 tw=99:
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#include "jit/ppc64le/MoveEmitter-ppc64le.h"

#include "jit/MacroAssembler-inl.h"

using namespace js;
using namespace js::jit;

void
MoveEmitterPPC64LE::emit(const MoveResolver& moves)
{
    if (moves.numCycles()) {
        // Reserve stack for cycle resolution
        masm.reserveStack(moves.numCycles() * sizeof(double));
        pushedAtCycle_ = masm.framePushed();
    }

    for (size_t i = 0; i < moves.numMoves(); i++)
        emit(moves.getMove(i));
}

Address
MoveEmitterPPC64LE::cycleSlot(uint32_t slot, uint32_t subslot) const
{
    int32_t offset = masm.framePushed() - pushedAtCycle_;
    MOZ_ASSERT(Imm16::IsInSignedRange(offset));
    return Address(StackPointer, offset + slot * sizeof(double) + subslot);
}

int32_t
MoveEmitterPPC64LE::getAdjustedOffset(const MoveOperand& operand)
{
    MOZ_ASSERT(operand.isMemoryOrEffectiveAddress());
    if (operand.base() != StackPointer)
        return operand.disp();

    // Adjust offset if stack pointer has been moved.
    return operand.disp() + masm.framePushed() - pushedAtStart_;
}

Address
MoveEmitterPPC64LE::getAdjustedAddress(const MoveOperand& operand)
{
    return Address(operand.base(), getAdjustedOffset(operand));
}


Register
MoveEmitterPPC64LE::tempReg()
{
    spilledReg_ = SecondScratchReg;
    return SecondScratchReg;
}

void
MoveEmitterPPC64LE::emitMove(const MoveOperand& from, const MoveOperand& to)
{
    if (from.isGeneralReg()) {
        // Second scratch register should not be moved by MoveEmitter.
        MOZ_ASSERT(from.reg() != spilledReg_);

        if (to.isGeneralReg())
            masm.movePtr(from.reg(), to.reg());
        else if (to.isMemory())
            masm.storePtr(from.reg(), getAdjustedAddress(to));
        else
            MOZ_CRASH("Invalid emitMove arguments.");
    } else if (from.isMemory()) {
        if (to.isGeneralReg()) {
            masm.loadPtr(getAdjustedAddress(from), to.reg());
        } else if (to.isMemory()) {
            masm.loadPtr(getAdjustedAddress(from), tempReg());
            masm.storePtr(tempReg(), getAdjustedAddress(to));
        } else {
            MOZ_CRASH("Invalid emitMove arguments.");
        }
    } else if (from.isEffectiveAddress()) {
        if (to.isGeneralReg()) {
            masm.computeEffectiveAddress(getAdjustedAddress(from), to.reg());
        } else if (to.isMemory()) {
            masm.computeEffectiveAddress(getAdjustedAddress(from), tempReg());
            masm.storePtr(tempReg(), getAdjustedAddress(to));
        } else {
            MOZ_CRASH("Invalid emitMove arguments.");
        }
    } else {
        MOZ_CRASH("Invalid emitMove arguments.");
    }
}

void
MoveEmitterPPC64LE::emitInt32Move(const MoveOperand &from, const MoveOperand &to)
{
    if (from.isGeneralReg()) {
        // Second scratch register should not be moved by MoveEmitter.
        MOZ_ASSERT(from.reg() != spilledReg_);

        if (to.isGeneralReg())
            masm.move32(from.reg(), to.reg());
        else if (to.isMemory())
            masm.store32(from.reg(), getAdjustedAddress(to));
        else
            MOZ_CRASH("Invalid emitInt32Move arguments.");
    } else if (from.isMemory()) {
        if (to.isGeneralReg()) {
            masm.load32(getAdjustedAddress(from), to.reg());
        } else if (to.isMemory()) {
            masm.load32(getAdjustedAddress(from), tempReg());
            masm.store32(tempReg(), getAdjustedAddress(to));
        } else {
            MOZ_CRASH("Invalid emitInt32Move arguments.");
        }
    } else if (from.isEffectiveAddress()) {
        if (to.isGeneralReg()) {
            masm.computeEffectiveAddress(getAdjustedAddress(from), to.reg());
        } else if (to.isMemory()) {
            masm.computeEffectiveAddress(getAdjustedAddress(from), tempReg());
            masm.store32(tempReg(), getAdjustedAddress(to));
        } else {
            MOZ_CRASH("Invalid emitInt32Move arguments.");
        }
    } else {
        MOZ_CRASH("Invalid emitInt32Move arguments.");
    }
}

void
MoveEmitterPPC64LE::emitFloat32Move(const MoveOperand& from, const MoveOperand& to)
{
    // Don't clobber the temp register if it's the source.
    MOZ_ASSERT_IF(from.isFloatReg(), from.floatReg() != ScratchFloat32Reg);
    MOZ_ASSERT_IF(to.isFloatReg(), to.floatReg() != ScratchFloat32Reg);

    // Direct FPR-GPR moves are unpossible on Power and it shouldn't happen anyway.
    if (from.isFloatReg()) {
        if (to.isFloatReg()) {
            masm.moveFloat32(from.floatReg(), to.floatReg());
        } else if (to.isGeneralReg()) {
            // Don't bother handling this case.
            MOZ_CRASH("emitFloat32Move -> GPR not allowed on PowerPC");
        } else {
            MOZ_ASSERT(to.isMemory());
            masm.storeFloat32(from.floatReg(), getAdjustedAddress(to));
        }
    } else if (to.isFloatReg()) {
        MOZ_ASSERT(from.isMemory());
        masm.loadFloat32(getAdjustedAddress(from), to.floatReg());
    } else if (to.isGeneralReg()) {
        MOZ_ASSERT(from.isMemory());
        masm.loadPtr(getAdjustedAddress(from), to.reg());
    } else {
        MOZ_ASSERT(from.isMemory());
        MOZ_ASSERT(to.isMemory());
        masm.loadFloat32(getAdjustedAddress(from), ScratchFloat32Reg);
        masm.storeFloat32(ScratchFloat32Reg, getAdjustedAddress(to));
    }
}

// This is almost the same.
void
MoveEmitterPPC64LE::emitDoubleMove(const MoveOperand& from, const MoveOperand& to)
{
    // Don't clobber the temp register if it's the source.
    MOZ_ASSERT_IF(from.isFloatReg(), from.floatReg() != ScratchFloat32Reg);
    MOZ_ASSERT_IF(to.isFloatReg(), to.floatReg() != ScratchFloat32Reg);

    if (from.isFloatReg()) {
        if (to.isFloatReg()) {
            masm.moveDouble(from.floatReg(), to.floatReg());
        } else if (to.isGeneralReg()) {
            // Maximum bogosity again, dude.
            MOZ_CRASH("emitDoubleMove FPR -> GPR not allowed on PowerPC");
        } else {
            MOZ_ASSERT(to.isMemory());
            masm.storeDouble(from.floatReg(), getAdjustedAddress(to));
        }
    } else if (to.isFloatReg()) {
        MOZ_ASSERT(from.isMemory());
        masm.loadDouble(getAdjustedAddress(from), to.floatReg());
    } else if (to.isGeneralReg()) {
        // Not handled (yet?)
        MOZ_CRASH("emitDoubleMove mem -> GPR not allowed on PowerPC");
    } else {
        MOZ_ASSERT(from.isMemory());
        MOZ_ASSERT(to.isMemory());
        masm.loadDouble(getAdjustedAddress(from), ScratchDoubleReg);
        masm.storeDouble(ScratchDoubleReg, getAdjustedAddress(to));
    }
}

void
MoveEmitterPPC64LE::breakCycle(const MoveOperand& from, const MoveOperand& to,
                              MoveOp::Type type, uint32_t slotId)
{
    // There is some pattern:
    //   (A -> B)
    //   (B -> A)
    //
    // This case handles (A -> B), which we reach first. We save B, then allow
    // the original move to continue.
    switch (type) {
      case MoveOp::FLOAT32:
        if (to.isMemory()) {
            FloatRegister temp = ScratchFloat32Reg;
            masm.loadFloat32(getAdjustedAddress(to), temp);
            masm.storeFloat32(temp, cycleSlot(slotId));
        } else {
            masm.storeFloat32(to.floatReg(), cycleSlot(slotId));
        }
        break;
      case MoveOp::DOUBLE:
        if (to.isMemory()) {
            FloatRegister temp = ScratchDoubleReg;
            masm.loadDouble(getAdjustedAddress(to), temp);
            masm.storeDouble(temp, cycleSlot(slotId));
        } else {
            masm.storeDouble(to.floatReg(), cycleSlot(slotId));
        }
        break;
      case MoveOp::INT32:
        if (to.isMemory()) {
            Register temp = tempReg();
            masm.load32(getAdjustedAddress(to), temp);
            masm.store32(temp, cycleSlot(0));
        } else {
            // Second scratch register should not be moved by MoveEmitter.
            MOZ_ASSERT(to.reg() != spilledReg_);
            masm.store32(to.reg(), cycleSlot(0));
        }
        break;
      case MoveOp::GENERAL:
        if (to.isMemory()) {
            Register temp = tempReg();
            masm.loadPtr(getAdjustedAddress(to), temp);
            masm.storePtr(temp, cycleSlot(0));
        } else {
            // Second scratch register should not be moved by MoveEmitter.
            MOZ_ASSERT(to.reg() != spilledReg_);
            masm.storePtr(to.reg(), cycleSlot(0));
        }
        break;
      default:
        MOZ_CRASH("Unexpected move type");
    }
}

void
MoveEmitterPPC64LE::completeCycle(const MoveOperand& from, const MoveOperand& to,
                                 MoveOp::Type type, uint32_t slotId)
{
    // There is some pattern:
    //   (A -> B)
    //   (B -> A)
    //
    // This case handles (B -> A), which we reach last. We emit a move from the
    // saved value of B, to A.
    switch (type) {
      case MoveOp::FLOAT32:
        if (to.isMemory()) {
            FloatRegister temp = ScratchFloat32Reg;
            masm.loadFloat32(cycleSlot(slotId), temp);
            masm.storeFloat32(temp, getAdjustedAddress(to));
        } else {
            masm.loadFloat32(cycleSlot(slotId), to.floatReg());
        }
        break;
      case MoveOp::DOUBLE:
        if (to.isMemory()) {
            FloatRegister temp = ScratchDoubleReg;
            masm.loadDouble(cycleSlot(slotId), temp);
            masm.storeDouble(temp, getAdjustedAddress(to));
        } else {
            masm.loadDouble(cycleSlot(slotId), to.floatReg());
        }
        break;
      case MoveOp::INT32:
        MOZ_ASSERT(slotId == 0);
        if (to.isMemory()) {
            Register temp = tempReg();
            masm.load32(cycleSlot(0), temp);
            masm.store32(temp, getAdjustedAddress(to));
        } else {
            // Second scratch register should not be moved by MoveEmitter.
            MOZ_ASSERT(to.reg() != spilledReg_);
            masm.load32(cycleSlot(0), to.reg());
        }
        break;
      case MoveOp::GENERAL:
        MOZ_ASSERT(slotId == 0);
        if (to.isMemory()) {
            Register temp = tempReg();
            masm.loadPtr(cycleSlot(0), temp);
            masm.storePtr(temp, getAdjustedAddress(to));
        } else {
            // Second scratch register should not be moved by MoveEmitter.
            MOZ_ASSERT(to.reg() != spilledReg_);
            masm.loadPtr(cycleSlot(0), to.reg());
        }
        break;
      default:
        MOZ_CRASH("Unexpected move type");
    }
}

void
MoveEmitterPPC64LE::emit(const MoveOp& move)
{
    const MoveOperand& from = move.from();
    const MoveOperand& to = move.to();

    if (move.isCycleEnd() && move.isCycleBegin()) {
        // A fun consequence of aliased registers is you can have multiple
        // cycles at once, and one can end exactly where another begins.
        breakCycle(from, to, move.endCycleType(), move.cycleBeginSlot());
        completeCycle(from, to, move.type(), move.cycleEndSlot());
        return;
    }

    if (move.isCycleEnd()) {
        MOZ_ASSERT(inCycle_);
        completeCycle(from, to, move.type(), move.cycleEndSlot());
        MOZ_ASSERT(inCycle_ > 0);
        inCycle_--;
        return;
    }

    if (move.isCycleBegin()) {
        breakCycle(from, to, move.endCycleType(), move.cycleBeginSlot());
        inCycle_++;
    }

    switch (move.type()) {
      case MoveOp::FLOAT32:
        emitFloat32Move(from, to);
        break;
      case MoveOp::DOUBLE:
        emitDoubleMove(from, to);
        break;
      case MoveOp::INT32:
        emitInt32Move(from, to);
        break;
      case MoveOp::GENERAL:
        emitMove(from, to);
        break;
      default:
        MOZ_CRASH("Unexpected move type");
    }
}

void
MoveEmitterPPC64LE::assertDone()
{
    MOZ_ASSERT(inCycle_ == 0);
}

void
MoveEmitterPPC64LE::finish()
{
    assertDone();

    masm.freeStack(masm.framePushed() - pushedAtStart_);
}
