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
```

## Key missing features

- Expressions that contain `::` or `S` may currently confuse the solvers. Such expressions should automatically be rewritten in terms of `++` and `+`.
- `=` types are often used in conjunction with Idris's `rewrite ... in` feature. It should be possible to write elaborators that can automate such uses further. For example, in the `plusCommutativeRewrite` example the user would ideally not have to spell out the `r + l = l + r` equality.

## Installation

1. Download the Rekenaar source code and open it in the terminal.
2. Run `idris --install rekenaar.ipkg`.

The Rekenaar package will be installed in `$(idris --libdir)/rekenaar`.

To experiment, type `idris -prekenaar` in the terminal:

```
Idris> :module Rekenaar
*Rekenaar> :let thm = the ((l, r : Nat) -> l + r = r + l) (%runElab natPlusRefl)
*Rekenaar> :t thm
thm : (l : Nat) -> (r : Nat) -> plus l r = plus r l
*Rekenaar> thm 3 4
Refl : 7 = 7
```

If you want to use Rekenaar in your own project, make sure to include `-prekenaar` in the `opts` field of your `.ipkg` file.

## Namespaces

### `Rekenaar`

The [Rekenaar module](src/Rekenaar.idr) contains the main API.

### `Rekenaar.Infer`

Verified solvers for algebraic structures.

Ideally Rekenaar will eventually support the following algebraic structures:

- [x] Monoids cover `⟨List a, [], ++⟩` (`Interfaces.Verified.VerifiedMonoid`)
- [x] Commutative monoids cover `⟨Nat, 0, +⟩` (`Rekenaar.Infer.CommutativeMonoid.VerifiedCommutativeMonoid`)
- [ ] Abelian groups cover `⟨ZZ, 0, +⟩` (`Interfaces.Verified.VerifiedAbelianGroup`)
- [ ] Commutative rings cover `ZZ` with `+` and `*` (`Interfaces.Verified.VerifiedRingWithUnity`)
- [ ] A Presburger arithmetic solver that covers, at a minimum, `⟨Nat, +, 0⟩` with `=` and `LTE` relations

The module `Rekenaar.Infer.Monoid` is based on chapter 3 of the report [Evidence-providing problem solvers in Agda](https://github.com/umazalakain/fyp).

The module `Rekenaar.Infer.CommutativeMonoid` started out as a copy of `Rekenaar.Infer.Monoid`. One open task is to make these two modules share more code.

### `Rekenaar.Reflect`

This namespace contains code that bridges the world of quotes `Raw` terms and the world of values.

Key functionality:

- Parse quoted `Raw` terms so that they can be processed by `Rekenaar.Infer` modules
- Given a proof that two terms are equal, return a quoted `Raw` value of this proof
- Utility functions for working with `Raw` values

### `Rekenaar.Elab`

Elaborator reflection scripts for invoking the solvers.

Goals include:

- [x] Elaborator scripts for producing `=` values
- [ ] Logic for rewriting `List.(::)` or `Nat.S` function applications in terms of `List.(++)` or `Nat.plus` before running the solvers
- [ ] Elaborator script that given a guess and a goal type, figures out how to rewrite the goal type to make the guess fit (e.g. rewrite `Vect (n + m) a` into `Vect (m + n) a`)
- [ ] Elaborator script for replacing multiplication of a stuck term by a constant (e.g. `3 * n`), with repeated addition of the stuck term (e.g. `n + n + n`)
- [ ] Logic for automatically resolving the interface implementation, element type, neutral value, and binary operation(s)
