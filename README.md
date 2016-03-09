Alive-NJ is a reimplementation of the [Automated LLVM's InstCombine Verifier][1],
written by Nuno Lopes, David Menendez, Santosh Nagarakatte, and John Regehr and
detailed in the paper ["Provably Correct Peephole Optimizations with Alive"][2],
presented at PLDI 2015.

[1]: https://github.com/nunoplopes/alive/
[2]: http://www.cs.utah.edu/~regehr/papers/pldi15.pdf

Alive-NJ is intended to facilitate experimentation with Alive semantics and
extension of Alive into new areas. It is not recommended for serious usage.

## Requirements

Alive requires Python 2.7 and Z3 4.3.2 or later.

Z3 can be obtained from https://github.com/Z3Prover/z3

## Usage

    ./run.py [file [file...]]
    ./run.py --help

Alive-NJ reads from standard input if no arguments are given.

## Differences from Alive

Alive-NJ adds these features:

* Support for floating-point
    * `half`, `float`, and `double` types
    * Instructions: `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fcmp`,
      `fptosi`, `fptoui`, `sitofp`, `uitofp`, `fpext`, `fptrunc`
    * Symbolic constants, integer literals, and expressions using `+`, `-`,
      `*`, `/`, and `%` may be integer or floating point
    * Floating-point literals
    * Special values `nan`, `inf`, `-inf`, and `-0.0`
    * Precondition comparisons use IEEE semantics for floats (thus,
      `C == 0.0` is satisfied when `C` is positive or negative zero,
      and `C == nan` is never satisfied)
    * Predicate `fpsame(C1,C2)` is satisfied when `C1` and `C2` are
      *structurally* equal (meaning `fpsame(nan,nan)` is true, but
      `fpsame(0.0, -0.0)` is not)
* Full replaceability of `undef`: If `%x` is `undef`, then `xor %x, %x` is
  `undef`
* New constant symbols may be defined in the target, for example, 
  `C2 = trunc(C1)`. These symbols are in scope in the precondition and target,
  so `zext(C2) == C1` is a valid precondition. Note that, unlike `trunc(C1)`,
  all uses of `C2` will have the same type.

Alive-NJ does not include, or does not fully implement, these features:

* C++ code generation
* Flag inference
* Memory operations (`alloca`, `store`, `load`, `getelementpointer`)
* Pointer types
* Composition of optimizations and non-termination checking
