# Rekenaar

[Idris](https://www.idris-lang.org) compile-time tactics for solving equations involving monoids and commutative monoids:

- Monoids are algebraic structures with an associative binary operation and a neutral element. E.g. `(List a, ++, [])` is a monoid.
- Commutative monoids are monoids where the binary operation is commutative (in addition to being associative). E.g. `(Nat, +, 0)` is a commutative monoid.

The tactics make use of Idris's [Elaborator Reflection](http://docs.idris-lang.org/en/v1.3.0/reference/elaborator-reflection.html). They first inspect the goal type and then attempt to fill in a value (proof) for that type.
 
See [here](src/Test/Examples) for examples on what's currently possible.

Known limitations:

- Expressions that contain `::` or `S` or `minus` may currently confuse the solvers
- The tactics can currently not resolve typeclasses or determine the names of the binary operator and neutral elements

Fixing these issues shouldn't be difficult and is high on the priority list.

## Namespaces

### `Rekenaar.Infer`

Verified solvers for algebraic structures.

Initial code is based on the report [Evidence-providing problem solvers in Agda](https://github.com/umazalakain/fyp). This report covers the following structures:

- [x] Solver for monoids (`Interfaces.Verified.VerifiedMonoid`)
- [ ] Solver for commutative rings (`Interfaces.Verified.VerifiedRingWithUnity`)
- [ ] Solver for Presburger arithmetic (`Decidable.Order.Ordered`)

So far, the first solver has been implemented in Rekenaar. The module `Rekenaar.Infer.CommutativeMonoid` also contains a variant of this solver, with an added understanding of commutativity.

Ideally Rekenaar will eventually support the following algebraic structures:

- [x] Monoids cover `List a` with `++` (`Interfaces.Verified.VerifiedMonoid`)
- [x] Commutative monoids cover `Nat` with `+` (`Rekenaar.Infer.CommutativeMonoid.VerifiedCommutativeMonoid`)
- [ ] Abelian groups cover `ZZ` with `+` (`Interfaces.Verified.VerifiedAbelianGroup`)
- [ ] Commutative rings cover `ZZ` with `+` and `*` (`Interfaces.Verified.VerifiedRingWithUnit`)
- [ ] Informally, a Presburger arithmetic solver can be expected to cover, at a minimum, `⟨Nat, +, =, LTE⟩`

### `Rekenaar.Reflect`

This namespace contains code that bridges the world of quotes `Raw` terms and the world of values.

Key functionality:

- Parse quoted `Raw` terms so that they can be processed by `Rekenaar.Infer` modules
- Given a proof that two terms are equal, return a quoted `Raw` value of this proof

### `Rekenaar.Elab`

Elaborator reflection scripts for invoking the solvers.

Notably missing:

- Logic for automatically resolving the interface implementation, element type, neutral value, and binary operation(s)
- Elaborator script for rewriting `List.(::)` or `Nat.S` function applications in terms of `List.(++)` or `Nat.plus`
- Elaborator script for replacing multiplication of a stuck term by a constant (e.g. `3 * n`), with repeated addition of the stuck term (e.g. `n + n + n`)
- Elaborator script that given a guess and a goal type, figures out how to rewrite the goal type to make the guess fit (e.g. rewrite `Vect (n + m) a` into `Vect (m + n) a`)

