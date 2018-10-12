module Monoid

import Data.Fin
import Data.Vect

-- contrib
import Interfaces.Verified

import Rekenaar.Infer.Common

%default total
%access private

public export
normalize : Expr cnt -> NormalForm cnt
normalize = Common.normalizeMonoid

sound : (VerifiedMonoid ty) => (expr : Expr cnt) -> (env : Env cnt ty) -> eval env expr = evalNF env (normalize expr)
sound Neutral env = Refl
sound (Var i) env = sym $ monoidNeutralIsNeutralL $ index env i
sound (lhs <+> rhs) env =
  rewrite sound lhs env in
  rewrite sound rhs env in
  homNF env (normalize lhs) (normalize rhs)

public export
Solution : (VerifiedMonoid ty) => (lhs, rhs : Expr cnt) -> Type
Solution {ty} lhs rhs = (env : Env cnt ty) -> eval env lhs = eval env rhs

export
solve : (m : VerifiedMonoid ty) => (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Solution @{m} lhs rhs
solve lhs rhs sameNF env =
  rewrite sound lhs env in
  rewrite sameNF in
  sym $ sound rhs env
