# Rekenaar

WIP Idris compile-time tactics for monoids and other algebraic structures.

Currently one solver is included. The solver can produce equalities for algebraic structures with an associative binary operation and a neutral elements (that is, monoids such as `List a, ++, []`).

The following new features are highest on the priority list:

- Support for commutative monoids (e.g. `Nat, +, 0`)
- Improved usability via additional elaborator reflection magic

See [here](src/Test/Examples) for examples on what's currently possible.

## Namespaces

### `Rekenaar.Infer`

Verified solvers for algebraic structures.

Initial code is based on the report [Evidence-providing problem solvers in Agda](https://github.com/umazalakain/fyp). This report covers the following structures:

- [x] Solver for monoids (`Interfaces.Verified.VerifiedMonoid`)
- [ ] Solver for commutative rings (`Interfaces.Verified.VerifiedRingWithUnity`)
- [ ] Solver for Presburger arithmetic (`Decidable.Order.Ordered`)

Here's what this means:

- `Interfaces.Verified.VerifiedMonoid` covers `List a` with `++`
- Commutative monoids cover `Nat` with `+`, but Idris does not appear to natively have an interface for such structures
- `Interfaces.Verified.VerifiedAbelianGroup` covers `ZZ` with `+` (and `-`)
- `Interfaces.Verified.VerifiedRingWithUnit` covers `ZZ` with `+` (and `-`) and `*`
- A Presburger arithmetic solver should, at a minimum, cover `Nat, +, =, LTE`

### `Rekenaar.Reflect`

This namespace contains code that bridges the world of quotes `Raw` terms and the world of values.

- Parse quoted `Raw` terms so that they can be processed by `Rekenaar.Infer` modules
- Given a proof that two terms are equal, return a quoted `Raw` value of this proof

### `Rekenaar.Elab`

Elaborator reflection scripts for invoking the solvers.

Notably missing:

- Logic for automatically resolving the interface implementation, element type, neutral value, and binary operation(s)
- Elaborator script for rewriting `List.(::)` or `Nat.S` function applications in terms of `List.(++)` or `Nat.plus`
- Elaborator script for replacing multiplication of a stuck term by a constant (e.g. `3 * n`), with repeated addition of the stuck term (e.g. `n + n + n`)
- Elaborator script that given a guess and a goal type, figures out how to rewrite the goal type to make the guess fit (e.g. rewrite `Vect (n + m) a` into `Vect (m + n) a`)

