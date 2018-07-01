module Monoid

import Data.Fin
import Data.Vect

-- contrib
import Interfaces.Verified

%default total
%access private

public export
data Expr : Nat -> Type where
  Var : Fin cnt -> Expr cnt
  Neutral : Expr cnt
  (<+>) : (lhs, rhs : Expr cnt) -> Expr cnt

public export
NormalForm : Nat -> Type
NormalForm cnt = List (Fin cnt)

public export
normalize : Expr cnt -> NormalForm cnt
normalize (Var i) = [i]
normalize Neutral = []
normalize (lhs <+> rhs) = normalize lhs ++ normalize rhs

public export
data Env : VerifiedMonoid ty -> Nat -> Type where
  MkEnv : {m : VerifiedMonoid ty} -> Vect cnt ty -> Env m cnt

public export
eval : {m : VerifiedMonoid ty} -> Expr cnt -> Env m cnt -> ty
eval (Var i) (MkEnv xs) = i `index` xs
eval Neutral _ = neutral
eval (lhs <+> rhs) env = eval lhs env <+> eval rhs env

evalNF : {m : VerifiedMonoid ty} -> NormalForm cnt -> Env m cnt -> ty
evalNF [] _ = neutral
evalNF (i::is) (MkEnv xs) {m} = (i `index` xs) <+> evalNF {m} is (MkEnv xs)

homomNF : {m : VerifiedMonoid ty} -> (is, js : NormalForm cnt) -> (env : Env m cnt) -> (evalNF {m} is env <+> evalNF js env) = evalNF (is ++ js) env
homomNF [] js env {m} = monoidNeutralIsNeutralR $ evalNF {m} js env
homomNF (i::is) js (MkEnv xs) {m} =
  let indLemma = homomNF {m} is js (MkEnv xs)
      iLookup = i `index` xs
      isEval = evalNF {m} is (MkEnv xs)
      jsEval = evalNF {m} js (MkEnv xs)
      assocLemma = sym $ semigroupOpIsAssociative iLookup isEval jsEval in
  replace {P = \var => iLookup <+> isEval <+> jsEval = iLookup <+> var} indLemma assocLemma

correct : (expr : Expr cnt) -> (env : Env m cnt) -> eval expr env = evalNF (normalize expr) env
correct Neutral env {m} = Refl
correct (Var i) (MkEnv xs) {m} = sym $ monoidNeutralIsNeutralL $ i `index` xs
correct (lhs <+> rhs) env {m} =
  rewrite correct lhs env in
  rewrite correct rhs env in
  rewrite homomNF (normalize lhs) (normalize rhs) env in
  Refl

public export
Solution : VerifiedMonoid ty -> (lhs, rhs : Expr cnt) -> Type
Solution m lhs rhs =
  (env : Env m cnt) -> eval lhs env = eval rhs env

export
solve : {m : VerifiedMonoid ty} -> (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Solution m lhs rhs
solve lhs rhs sameNF env =
  rewrite correct lhs env in
  rewrite sameNF in
  rewrite sym $ correct rhs env in
  Refl
