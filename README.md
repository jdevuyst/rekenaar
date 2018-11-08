# Rekenaar

[Idris](https://www.idris-lang.org) compile-time tactics for solving equations involving monoids and commutative monoids:

- Monoids are algebraic structures with an associative binary operation and a neutral element. E.g. `⟨List a, [], ++⟩` is a monoid.
- Commutative monoids are monoids where the binary operation is commutative (in addition to being associative). E.g. `⟨Nat, 0, +⟩` is a commutative monoid.

The tactics make use of Idris's [Elaborator Reflection](http://docs.idris-lang.org/en/v1.3.0/reference/elaborator-reflection.html). They first inspect the goal type and then attempt to fill in a value (proof) for that type.

## Examples

Here are a few simple examples that demonstrate what Rekenaar can do:

```idris
import Rekenaar
import Data.Fin

%language ElabReflection

plusCommutative : (l, r : Nat) -> l + r = r + l
plusCommutative = %runElab natPlusRefl

plusCommutativeRewrite : (l, r : Nat) -> Fin (l + r) -> Fin (r + l)
plusCommutativeRewrite l r fin = rewrite the (r + l = l + r) (%runElab natPlusRefl) in fin

plusCommutativeRewrite' : (l, r : Nat) -> Fin (l + r) -> Fin (r + l)
plusCommutativeRewrite' = %runElab natPlusRewrite

succSuccPlusTwo : (n : Nat) -> S (S n) = n + 2
succSuccPlusTwo = %runElab natPlusRefl
```

For more realistic examples, see [this commit](https://github.com/jdevuyst/idris-data/commit/771f62863f56b0bb7c1a0a9fddc9a48e55224143), in which an Idris project was modified to use Rekenaar.

There's also a [video tutorial](https://www.youtube.com/watch?v=deYYhTl4zDs):

[![Demo of Rekenaar](http://img.youtube.com/vi/deYYhTl4zDs/0.jpg)](http://www.youtube.com/watch?v=deYYhTl4zDs)

## Installation

1. Download the Rekenaar source code and open it in the terminal.
2. Run `idris --install rekenaar.ipkg`.

The Rekenaar package will be installed in `$(idris --libdir)/rekenaar`.

To experiment, type `idris -p rekenaar` in the terminal:

```
Idris> :module Rekenaar
*Rekenaar> :let thm = the ((l, r : Nat) -> l + r = r + l) (%runElab natPlusRefl)
*Rekenaar> :t thm
thm : (l : Nat) -> (r : Nat) -> plus l r = plus r l
*Rekenaar> thm 3 4
Refl : 7 = 7
```

If you want to use Rekenaar in your own project, make sure to include `-p rekenaar` in the `opts` field of your `.ipkg` file.

## Namespaces

### `Rekenaar`

The [Rekenaar module](src/Rekenaar.idr) contains the main API. There's a bit of ad hoc code for each structure, which helps with usability.

Monoids:

- [x] `listRefl`
- [ ] `listRewrite`

Commutative monoids:

- [x] `natPlusRefl`
- [x] `natPlusRewrite`
- [x] `natMultRefl` (may require a `%freeze mult` directive at the call site)
- [x] `natMultRewrite`

The `natMultRefl` solver could use some more ad hoc code so as to eliminate the need for the `%freeze` directive. It also does not understand constants yet (treating them as opaque variables).

`natPlusRewrite` could also be [improved](https://github.com/jdevuyst/rekenaar/issues/2).

### `Rekenaar.Infer`

Verified solvers for algebraic structures.

Ideally Rekenaar will eventually support the following algebraic structures:

- [x] Monoids such as `⟨List a, [], ++⟩` (`Interfaces.Verified.VerifiedMonoid`)
- [x] Commutative monoids such as `⟨Nat, 0, +⟩` (`Rekenaar.Infer.CommutativeMonoid.VerifiedCommutativeMonoid`)
- [ ] Abelian groups such as `⟨ZZ, 0, +⟩` (`Interfaces.Verified.VerifiedAbelianGroup`)
- [ ] Commutative rings such as `ZZ` with `+` and `*` (`Interfaces.Verified.VerifiedRingWithUnity`)

Notes on the implementation:

- The module `Rekenaar.Infer.Monoid` is based on chapter 3 of the report [Evidence-providing problem solvers in Agda](https://github.com/umazalakain/fyp).
- There's no built-in support for constants at this point. For `⟨Nat, 0, +⟩` this is not a problem because the uncompute logic will rewrite `S (S ... x)` to `1 + 1 + ... + x`. However, for the general case we'll want to change the solver to understand constants.

### `Rekenaar.Reflect`

This namespace contains code that bridges the world of quotes `Raw` terms and the world of values.

Key functionality:

- Parse quoted `Raw` terms so that they can be processed by `Rekenaar.Infer` modules
- Given a proof that two terms are equal, return a quoted `Raw` value of this proof
- Utility functions for working with `Raw` values

### `Rekenaar.Elab`

Elaborator reflection scripts for invoking the solvers from `Rekenaar.Infer` and scripts for massaging expressions to make them more ammenable to being solved.

Goals include:

- [x] Elaborator scripts for producing `=` values
- [x] 'Uncompute' scripts for rewriting applications of succ/cons-like constructors (such as `List.(::)` or `Nat.S`) in terms of `<+>` before running the solvers
- [x] Elaborator script to make creating `f x -> f y` functions easy given a tactic that can prove that `x = y` (e.g. for generating functions such as `Vect (n + m) a -> Vect (m + n) a` given the `natPlusRefl` tactic)
- [ ] Elaborator script for replacing multiplication of a stuck term by a constant (e.g. `3 * n`), with repeated addition of the stuck term (e.g. `n + n + n`)

The implementation could be improved as follows:

- [ ] Logic for automatically resolving the interface implementation, element type, neutral value, and binary operation(s)
- [ ] Logic that, given a function such as `List.(++)`, `Nat.plus`, `Nat.mult`, can automatically create 'uncompute' transformations

## Related reading

- [Evidence-providing problem solvers in Agda](https://github.com/umazalakain/fyp)
- [Agda Ring Solver](http://www.cse.chalmers.se/~nad/listings/lib/Algebra.RingSolver.html)
- [RingIdris](https://github.com/FranckS/RingIdris): Ring solver for Idris 0.6, which does not presently compile for modern versions of Idris
- [Christiansen's monoid tactic](https://gist.github.com/david-christiansen/066ad771212b2f20ea40)
