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
normalize Neutral = neutral
normalize (lhs <+> rhs) = normalize lhs <+> normalize rhs

public export
data Env : VerifiedMonoid ty -> Nat -> Type where
  MkEnv : {m : VerifiedMonoid ty} -> Vect cnt ty -> Env m cnt

public export
index : {m : VerifiedMonoid ty} -> Env m cnt -> Fin cnt -> ty
index (MkEnv xs) i = i `index` xs

public export
eval : {m : VerifiedMonoid ty} -> Env m cnt -> Expr cnt -> ty
eval env (Var i) = index env i
eval env Neutral = neutral
eval env (lhs <+> rhs) = eval env lhs <+> eval env rhs

evalNF : {m : VerifiedMonoid ty} -> Env m cnt -> NormalForm cnt -> ty
evalNF {m} env = foldr (\i, acc => index env i <+> acc) neutral

homomNF : {m : VerifiedMonoid ty} -> (env : Env m cnt) -> (is, js : NormalForm cnt) ->
          (evalNF env is <+> evalNF env js) = evalNF env (is <+> js)
homomNF env [] js = monoidNeutralIsNeutralR $ evalNF env js
homomNF env (i::is) js =
  let indLemma = homomNF env is js
      iLookup = index env i
      isEval = evalNF env is
      jsEval = evalNF env js
      assocLemma = sym $ semigroupOpIsAssociative iLookup isEval jsEval
  in replace {P = \var => iLookup <+> isEval <+> jsEval = iLookup <+> var} indLemma assocLemma

sound : (expr : Expr cnt) -> (env : Env m cnt) -> eval env expr = evalNF env (normalize expr)
sound Neutral env = Refl
sound (Var i) env = sym $ monoidNeutralIsNeutralL $ index env i
sound (lhs <+> rhs) env =
  rewrite sound lhs env in
  rewrite sound rhs env in
  homomNF env (normalize lhs) (normalize rhs)

public export
Solution : VerifiedMonoid ty -> (lhs, rhs : Expr cnt) -> Type
Solution m lhs rhs = (env : Env m cnt) -> eval env lhs = eval env rhs

export
solve : {m : VerifiedMonoid ty} -> (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Solution m lhs rhs
solve lhs rhs sameNF env =
  rewrite sound lhs env in
  rewrite sameNF in
  sym $ sound rhs env
