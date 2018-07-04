module CommutativeMonoid

import Data.Fin
import Data.Vect

-- contrib
import Data.ZZ
import Decidable.Order
import Interfaces.Verified

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

data Expr : Nat -> Type where
  Var : Fin cnt -> Expr cnt
  Neutral : Expr cnt
  (<+>) : (lhs, rhs : Expr cnt) -> Expr cnt

NormalForm : Nat -> Type
NormalForm cnt = List (Fin cnt)

normalize_ : Expr cnt -> NormalForm cnt
normalize_ (Var i) = [i]
normalize_ Neutral = []
normalize_ (lhs <+> rhs) = normalize_ lhs ++ normalize_ rhs

data Env : VerifiedCommutativeMonoid ty -> Nat -> Type where
  MkEnv : {m : VerifiedCommutativeMonoid ty} -> Vect cnt ty -> Env m cnt

eval : {m : VerifiedCommutativeMonoid ty} -> Expr cnt -> Env m cnt -> ty
eval (Var i) (MkEnv xs) = i `index` xs
eval Neutral _ = neutral
eval (lhs <+> rhs) env = eval lhs env <+> eval rhs env

evalNF : {m : VerifiedCommutativeMonoid ty} -> NormalForm cnt -> Env m cnt -> ty
evalNF [] _ = neutral
evalNF (i::is) (MkEnv xs) {m} = (i `index` xs) <+> evalNF {m} is (MkEnv xs)

homomNF : {m : VerifiedCommutativeMonoid ty} -> (is, js : NormalForm cnt) -> (env : Env m cnt) -> (evalNF {m} is env <+> evalNF js env) = evalNF (is ++ js) env
homomNF [] js env {m} = monoidNeutralIsNeutralR $ evalNF {m} js env
homomNF (i::is) js (MkEnv xs) {m} =
  let indLemma = homomNF {m} is js (MkEnv xs)
      iLookup = i `index` xs
      isEval = evalNF {m} is (MkEnv xs)
      jsEval = evalNF {m} js (MkEnv xs)
      assocLemma = sym $ semigroupOpIsAssociative iLookup isEval jsEval in
  replace {P = \var => iLookup <+> isEval <+> jsEval = iLookup <+> var} indLemma assocLemma

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
sortNF {cnt} expr = sortNF_ cnt expr

commAssoc : VerifiedCommutativeMonoid ty => {l, c, r, rhs : ty} -> l <+> (c <+> r) = rhs -> c <+> (l <+> r) = rhs
commAssoc eq {l} {c} {r} {rhs} =
  let eq = replace {P=\expr => expr = rhs} (semigroupOpIsAssociative l c r) eq
      eq = replace {P=\expr => expr <+> r = rhs} (semigroupOpIsCommutative l c) eq
      eq = replace {P=\expr => expr = rhs} (sym $ semigroupOpIsAssociative c l r) eq
      in eq

sortLemma1 : {m : VerifiedCommutativeMonoid ty} -> (nf : NormalForm cnt) -> (env : Env m cnt) -> evalNF {m} nf env = evalNF {m} (sortNF1 nf) env
sortLemma1 [] env = Refl
sortLemma1 [x] env = Refl
sortLemma1 (x::y::zs) (MkEnv {m} vals) with (x <= y)
  | True = let ind = assert_total $ sortLemma1 {m} (y::zs) (MkEnv {m} vals) in
            cong {f=(<+>) (index x vals)} ind
  | False = let ind = assert_total $ sortLemma1 {m} (x::zs) (MkEnv {m} vals) in
            let ind' = cong {f=(<+>) (index y vals)} ind in
            commAssoc ind'

sortLemma_ : {m : VerifiedCommutativeMonoid ty} -> (nf : NormalForm cnt) -> (env : Env m cnt) -> evalNF {m} nf env = evalNF {m} (sortNF_ n nf) env
sortLemma_ {n=Z} {m} nf env = Refl
sortLemma_ {n=S n'} {m} nf env =
  let ind = sortLemma_ {n=n'} {m} nf env in
  let prf = sortLemma1 {m} (sortNF_ n' nf) env in
  rewrite sym prf in
  ind

sortLemma : {m : VerifiedCommutativeMonoid ty} -> (nf : NormalForm cnt) -> (env : Env m cnt) -> evalNF {m} nf env = evalNF {m} (sortNF nf) env
sortLemma [] _ = Refl
sortLemma [x] _ = Refl
sortLemma {cnt} {m} (x::y::zs) env = sortLemma_ {n=cnt} {m} (x::y::zs) env

correct : (expr : Expr cnt) -> (env : Env m cnt) -> eval expr env = evalNF (sortNF (normalize_ expr)) env
correct Neutral env {m} = Refl
correct (Var i) (MkEnv xs) {m} = sym $ monoidNeutralIsNeutralL $ i `index` xs
correct (lhs <+> rhs) env {m} =
  rewrite correct lhs env in
  rewrite correct rhs env in
  rewrite sym $ sortLemma (normalize_ lhs) env in
  rewrite sym $ sortLemma (normalize_ rhs) env in
  rewrite sym $ sortLemma (normalize_ lhs ++ normalize_ rhs) env in
  rewrite homomNF (normalize_ lhs) (normalize_ rhs) env in
  Refl

Solution : VerifiedCommutativeMonoid ty -> (lhs, rhs : Expr cnt) -> Type
Solution m lhs rhs =
  (env : Env m cnt) -> eval lhs env = eval rhs env

normalize : Expr cnt -> NormalForm cnt
normalize = sortNF . normalize_

solve : {m : VerifiedCommutativeMonoid ty} -> (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Solution m lhs rhs
solve lhs rhs sameNF env =
  rewrite correct lhs env in
  rewrite sameNF in
  rewrite sym $ correct rhs env in
  Refl
