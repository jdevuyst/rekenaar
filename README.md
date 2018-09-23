# Rekenaar

[Idris](https://www.idris-lang.org) compile-time tactics for solving equations involving monoids and commutative monoids:

- Monoids are algebraic structures with an associative binary operation and a neutral element. E.g. `⟨List a, [], ++⟩` is a monoid.
- Commutative monoids are monoids where the binary operation is commutative (in addition to being associative). E.g. `⟨Nat, 0, +⟩` is a commutative monoid.

The tactics make use of Idris's [Elaborator Reflection](http://docs.idris-lang.org/en/v1.3.0/reference/elaborator-reflection.html). They first inspect the goal type and then attempt to fill in a value (proof) for that type.

## Examples

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

The [Rekenaar module](src/Rekenaar.idr) contains the main API.

### `Rekenaar.Infer`

Verified solvers for algebraic structures.

Ideally Rekenaar will eventually support the following algebraic structures:

- [x] Monoids such as `⟨List a, [], ++⟩` (`Interfaces.Verified.VerifiedMonoid`)
- [x] Commutative monoids such as `⟨Nat, 0, +⟩` (`Rekenaar.Infer.CommutativeMonoid.VerifiedCommutativeMonoid`)
- [ ] Abelian groups such as `⟨ZZ, 0, +⟩` (`Interfaces.Verified.VerifiedAbelianGroup`)
- [ ] Commutative rings such as `ZZ` with `+` and `*` (`Interfaces.Verified.VerifiedRingWithUnity`)

Notes on the implementation:

- The module `Rekenaar.Infer.Monoid` is based on chapter 3 of the report [Evidence-providing problem solvers in Agda](https://github.com/umazalakain/fyp).
- The module `Rekenaar.Infer.CommutativeMonoid` started out as a copy of `Rekenaar.Infer.Monoid`. One open task is to make these two modules share more code.

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
