module Common

import Data.Fin
import Data.Vect

-- contrib
import Interfaces.Verified

%default total
%access public export

data Expr : Nat -> Type where
  Var : Fin cnt -> Expr cnt
  Neutral : Expr cnt
  (<+>) : (lhs, rhs : Expr cnt) -> Expr cnt

NormalForm : Nat -> Type
NormalForm cnt = List (Fin cnt)

normalizeMonoid : Expr cnt -> NormalForm cnt
normalizeMonoid (Var i) = [i]
normalizeMonoid Neutral = neutral
normalizeMonoid (lhs <+> rhs) = normalizeMonoid lhs <+> normalizeMonoid rhs

data Env : Nat -> Type -> Type where
  MkEnv : Vect cnt ty -> Env cnt ty

index : Env cnt ty -> Fin cnt -> ty
index (MkEnv xs) i = i `index` xs

eval : (m : VerifiedMonoid ty) => Env cnt ty -> Expr cnt -> ty
eval env (Var i) = index env i
eval env Neutral = neutral
eval env (lhs <+> rhs) = eval env lhs <+> eval env rhs

evalNF : (m : VerifiedMonoid ty) => Env cnt ty -> NormalForm cnt -> ty
evalNF env = foldr (\i, acc => index env i <+> acc) neutral

homomNF : (m : VerifiedMonoid ty) => (env : Env cnt ty) -> (is, js : NormalForm cnt) ->
          (evalNF env is <+> evalNF env js) = evalNF env (is <+> js)
homomNF env [] js = monoidNeutralIsNeutralR $ evalNF env js
homomNF env (i::is) js =
  let indLemma = homomNF env is js
      iLookup = index env i
      isEval = evalNF env is
      jsEval = evalNF env js
      assocLemma = sym $ semigroupOpIsAssociative iLookup isEval jsEval
  in replace {P = \var => iLookup <+> isEval <+> jsEval = iLookup <+> var} indLemma assocLemma
