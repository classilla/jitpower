# JITPOWER

This is a temporary staging ground for work on the Firefox ppc64 JIT. Once the MVP has been completed, the intention is to add it to the Firefox tree for maintenance as part of Firefox and this repo will eventually be removed.

## MVP Definition

The Minimum Viable Product is a POWER9 little-endian JIT with Wasm and without SIMD running with the 64-bit ELFv2 ABI and a 64K page size. There is certainly interest and value in big-endian and additional 64-bit PowerPC support (potentially all the way down to the 970/G5), but these can be grafted on after the fact and the SpiderMonkey JIT core is known to have endian problems which need fixing separately (see TenFourFox for more on that). Additionally, POWER9 is a viable desktop system thanks to the Raptor Talos family which developers are likely to already be using, and the new instructions in ISA 3.0 make initial porting substantially simpler on POWER9.

SIMD is a separate issue which will not be addressed during the MVP period, and isn't necessary to get the JIT off the ground on any platform.

## Work Phases

### Required For MVP

1. Create a first draft JIT using the existing MIPS64 LE sources from Fx62 as a scaffold. Fx62 was chosen simply because it was the version when the port was originally commenced; there's nothing special about it otherwise other than to eliminate churn with constantly integrating new changes. This step is already **in progress**.
1. Ensure the first draft JIT compiles. A temporary Fx62 tree will probably be uploaded to facilitate this.
1. Ensure the first draft JIT links (add any missing functions).
1. Ensure the first draft JIT passes all tests in Fx62 (all tests in `js/src/jit-test`, `js/src/tests` and `jsapi-tests`).
1. Forward port the first draft JIT to `mozilla-central` as the second draft JIT.
1. Ensure the second draft JIT compiles.
1. Ensure the second draft JIT links.
1. Repair any new test failures.
1. Submit to Bugzilla in separate patch sets (patches needed against the JIT core, and new files).

### In Scope But Not Required For MVP

1. Simulator support to allow automated testing.

### Not In Scope For MVP (but desirable)

Roughly in order of priority:

1. Support for POWER8 and earlier.
1. BE support.
1. Support for non-64K page sizes.
1. SIMD with VMX/VSX.

Please don't submit pull requests for these yet unless they are trivial.

## Phase 1: What's Done So Far (And Might Even Work)

Some of this code originates from TenFourFox's IonPower JIT.

- Ion code generator (`CodeGenerator*`)
- Baseline code generator (`BaselineCompiler*`)
- Baseline and shared inline cache code generators (`BaselineIC*`, `SharedIC*`)
- LIR (intermediate representation) design (`LIR*.h`)
- Basic lowering/strength reduction (`Lowering*`)
- Bailouts (`Bailouts*`)
- Move code generator (`MoveEmitter*`)
- Trampoline code generator (`Trampoline*.cpp`)

What's remaining to do:

- Check my work, because I'm an idiot
- Define `Architecture` and exact interal JIT ABI usage, including temporary registers; see [the ABI documentation](http://openpowerfoundation.org/wp-content/uploads/resources/leabi/content/ch_preface.html)
    - Current plan is to use `r0` and `r12` as temporary registers (regenerating `r12` when making PLT-like calls back to PPC64 ABI-compliant code through `mtctr` `bctr`); `r12` or some other non-`r0` register needed as an "address" holder
    - Try to enable use of as many GPRs and FPRs as possible
    - Don't define SPRs other than `lr` outside of our JIT backend since SpiderMonkey doesn't understand the concept
    - No vector registers for the MVP
- Create `MacroAssembler` (`ma_*` functions) based on those used by the code generators
- Create `Assembler` (`as_*` [native instructions] and `xs_*` [commonly accepted alternative mnemonics] functions) based on instructions issued by the code generators and the macro assembler

## Feel free to start on what you like

The original MIPS code from which the new source was cribbed and rewritten is provided. Don't remove these just in case we need to refer back to them for the original semantics.

All code is MPL 2.0 and you agree that by submitting a pull request, you automatically grant use of your work under that license.
