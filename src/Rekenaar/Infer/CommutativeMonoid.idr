module CommutativeMonoid

import Data.Fin
import Data.Vect

-- contrib
import Data.ZZ
import Decidable.Order
import Interfaces.Verified

import Rekenaar.Infer.Common

%default total
%access public export

interface (VerifiedMonoid ty) => VerifiedCommutativeMonoid ty where
  semigroupOpIsCommutative : (l, r : ty) -> l <+> r = r <+> l

[PlusNatCommMonoidV] VerifiedCommutativeMonoid Nat using PlusNatMonoidV where
  semigroupOpIsCommutative = plusCommutative

[MultNatCommMonoidV] VerifiedCommutativeMonoid Nat using MultNatMonoidV where
  semigroupOpIsCommutative = multCommutative

[PlusZZCommMonoidV] VerifiedCommutativeMonoid ZZ using PlusZZMonoidV where
  semigroupOpIsCommutative = plusCommutativeZ

[MultZZCommMonoidV] VerifiedCommutativeMonoid ZZ using MultZZMonoidV where
  semigroupOpIsCommutative = multCommutativeZ

sortNF1 : NormalForm cnt -> NormalForm cnt
sortNF1 [] = []
sortNF1 [x] = [x]
sortNF1 (x::y::zs) with (x <= y)
  | True = x :: (assert_total $ sortNF1 (y::zs))
  | False = y :: (assert_total $ sortNF1 (x::zs))

-- naive sort
sortNF_ : Nat -> NormalForm cnt -> NormalForm cnt
sortNF_ Z expr = expr
sortNF_ (S n) expr = sortNF1 $ sortNF_ n expr

sortNF : NormalForm cnt -> NormalForm cnt
sortNF [] = []
sortNF [x] = [x]
sortNF expr = sortNF_ (length expr) expr

commAssoc : VerifiedCommutativeMonoid ty => {l, c, r, rhs : ty} -> l <+> (c <+> r) = rhs -> c <+> (l <+> r) = rhs
commAssoc eq {l} {c} {r} {rhs} =
  let eq = replace {P=\expr => expr = rhs} (semigroupOpIsAssociative l c r) eq
      eq = replace {P=\expr => expr <+> r = rhs} (semigroupOpIsCommutative l c) eq
      eq = replace {P=\expr => expr = rhs} (sym $ semigroupOpIsAssociative c l r) eq
      in eq

sortLemma1 : VerifiedCommutativeMonoid ty => (nf : NormalForm cnt) -> (env : Env cnt ty) -> evalNF env nf = evalNF env (sortNF1 nf)
sortLemma1 [] env = Refl
sortLemma1 [x] env = Refl
sortLemma1 (x::y::zs) env with (x <= y)
  | True = let ind = assert_total $ sortLemma1 (y::zs) env in
            cong {f=(<+>) (index env x)} ind
  | False = let ind = assert_total $ sortLemma1 (x::zs) env in
            let ind' = cong {f=(<+>) (index env y)} ind in
            commAssoc ind'

sortLemma_ : VerifiedCommutativeMonoid ty => (nf : NormalForm cnt) -> (env : Env cnt ty) -> evalNF env nf = evalNF env (sortNF_ n nf)
sortLemma_ {n=Z} nf env = Refl
sortLemma_ {n=S n'} nf env =
  let ind = sortLemma_ {n=n'} nf env in
  let prf = sortLemma1 (sortNF_ n' nf) env in
  rewrite sym prf in
  ind

sortLemma : VerifiedCommutativeMonoid ty => (nf : NormalForm cnt) -> (env : Env cnt ty) -> evalNF env nf = evalNF env (sortNF nf)
sortLemma [] _ = Refl
sortLemma [x] _ = Refl
sortLemma {cnt} (x::y::zs) env =
  sortLemma_ {n = 2 + length zs} (x::y::zs) env

sound : VerifiedCommutativeMonoid ty => (expr : Expr cnt) -> (env : Env cnt ty) -> eval env expr = evalNF env (sortNF (normalizeMonoid expr))
sound Neutral env = Refl
sound (Var i) env = sym $ monoidNeutralIsNeutralL $ index env i
sound (lhs <+> rhs) env =
  rewrite sound lhs env in
  rewrite sound rhs env in
  rewrite sym $ sortLemma (normalizeMonoid lhs) env in
  rewrite sym $ sortLemma (normalizeMonoid rhs) env in
  rewrite sym $ sortLemma (normalizeMonoid lhs ++ normalizeMonoid rhs) env in
  homomNF env (normalizeMonoid lhs) (normalizeMonoid rhs)

Solution : VerifiedCommutativeMonoid ty => (lhs, rhs : Expr cnt) -> Type
Solution {ty} lhs rhs =
  (env : Env cnt ty) -> eval env lhs = eval env rhs

normalize : Expr cnt -> NormalForm cnt
normalize = sortNF . normalizeMonoid

solve : (m: VerifiedCommutativeMonoid ty) => (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Solution @{m} lhs rhs
solve lhs rhs sameNF env =
  rewrite sound lhs env in
  rewrite sameNF in
  rewrite sym $ sound rhs env in
  Refl
