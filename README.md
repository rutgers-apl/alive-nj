Alive-NJ is a reimplementation of the [Automated LLVM's InstCombine Verifier][1],
written by Nuno Lopes, David Menendez, Santosh Nagarakatte, and John Regehr and
detailed in the paper ["Provably Correct Peephole Optimizations with Alive"][2],
presented at PLDI 2015.

[1]: https://github.com/nunoplopes/alive/
[2]: http://www.cs.utah.edu/~regehr/papers/pldi15.pdf

Alive-NJ is intended to facilitate experimentation with Alive semantics and
extension of Alive into new areas. 

## Requirements

Alive requires Python 2.7 and Z3 4.3.2 or later.

Z3 can be obtained from https://github.com/Z3Prover/z3

## Verification

To verify all the optimizations in a file:

    ./run.py [file [file...]]

Alive-NJ reads from standard input if no arguments are given.

To get a list of options:

    ./run.py --help

## Differences from Alive

Alive-NJ adds these features:

* Support for floating-point
    * `half`, `float`, `double`, `fp128`, and `x86_fp80` types
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
* Checks for compile-time undefined behavior. For example, a precondition
  `C1 % C2 == 0` will be rejected unless `C2` is guaranteed to be nonzero.
* An explicit `poison` value.
* Support for the recently-proposed `freeze` instruction.
* Choice of semantics for verification, using the `--translator` option.
  Available translators include:
    * `smtundef` Uses `undef` when the conditions of fast-math attributes are
       violated.
    * `smtpoison` Uses `poison` when the conditions of fast-math attributes are
      violated.
    * `poisononly` Allows the `freeze` instruction, and prevents `poison`
      from propagating through the unchosen branch of a `select` instruction.

We have found the following bugs with the floating point support in Alive-NJ:

* https://llvm.org/bugs/show_bug.cgi?id=26863
* https://llvm.org/bugs/show_bug.cgi?id=27151
* https://llvm.org/bugs/show_bug.cgi?id=27153
* https://llvm.org/bugs/show_bug.cgi?id=26862
* https://llvm.org/bugs/show_bug.cgi?id=26746

Alive-NJ does not include, or does not fully implement, these features:

* C++ code generation
* Flag inference
* Memory operations (`alloca`, `store`, `load`, `getelementpointer`)
* Pointer types
* Composition of optimizations and non-termination checking


## Precondition Inference

Alive-NJ includes a tool for inferring preconditions for Alive optimizations,
detailed in the paper ["Alive-Infer: Data-Driven Precondition Inference for 
Peephole Optimizations in LLVM"][Alive-Infer]. You might use this tool if an
optimization you have developed is invalid, and you need to find a stronger
precondition, or if you want to weaken the precondition of an optimization so
that it can be used on more programs.

[Alive-Infer]: http://export.arxiv.org/abs/1611.05980

### Usage

To infer preconditions for all optimizations given in a file:

    ./infer.py [file [file...]]

Alive-Infer reads from standard input if no files are given.

To get a list of options:

    ./infer.py --help

Most options can be negated. For example, `--incompletes` vs `--no-incompletes`.
In case of a conflict, the last option wins.

Alive-Infer only returns preconditions which are valid, meaning they reject
all input programs where the optimization would change the semantics.
Alive-Infer attempts to find preconditions which accept *all* input programs
where the optimization is valid. This may result in too-complex preconditions,
or require too much time to run.

If `--incompletes` is set, Alive-Infer will also generate valid and succinct
preconditions which may exclude some input programs where the optimization is
valid.

### Input format

Alive-Infer extends the Alive language with headers which provide more
information to the inference engine. To illustrate:

    Name: AndOrXor:1628-1
    Feature: isPowerOf2(-C2 ^ -C1)
    Feature: -C2 ^ -C1 == (C3-C2) ^ (C3-C1)
    Feature: abs(C1-C2) u> C3
    Assume: C1 != 0 && C2 != 0
    Pre: C1 u> C3 && C2 u> C3 && isPowerOf2(C1 ^ C2)
      %a1     = add i29 %A, C1
      %a2     = add %A, C2
      %cmp1   = icmp ult %a1, C3
      %cmp2   = icmp ult %a2, C3
      %r      = or %cmp1, %cmp2
    =>
      %newand = and %A, ~(C1^C2)
      %newadd = add %newand, umax(C1, C2)
      %r      = icmp ult %newadd, C3

`Feature:` headers suggest predicates to the inference engine. Use
`--no-features` to ignore these headers.

`Assume:` headers indicate conditions that should never occur. The
precondition is not required to accept or reject input programs which violate
the assumptions. Use `--no-assumptions` to ignore these headers.

`Pre:` headers are normally ignored during inference. However, certain options
tell Alive-Infer to use this specified precondition:

* If `--pre-features` is set, Alive-Infer will treat the predicates in `Pre:` as
  if they had been suggested using `Feature:`.
* If `--assume-pre` is set, Alive-Infer will treat `Pre:` as if it were
  `Assume:`.
* If `--strengthen` is set, Alive-Infer will attempt to find a precondition
  which makes the optimization valid *and* implies the given precondition.

### Customization

If you find yourself using the same options frequently, you can customize
`infer.py` by creating a copy and adding keyword arguments to its call to
`main()`.

For example, to make `--pre-features` set by default, use:

    main(pre_features = True)

