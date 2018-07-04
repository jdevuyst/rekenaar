module Rekenaar.Reflect.CommutativeMonoid

import Control.Isomorphism
import Data.Fin
import Data.Vect

-- contrib
import Decidable.Equality
import Interfaces.Verified
import Language.Reflection.Utils

import public Rekenaar.Reflect.Utils
import Rekenaar.Infer.CommutativeMonoid

%default total
%access private

export
implementation Quotable (Expr cnt) Raw where
  quotedTy {cnt} = `(Expr ~(quote cnt))
  quote (Var idx) {cnt} = `(CommutativeMonoid.Var {cnt=~(quote cnt)} ~(quote idx))
  quote Neutral {cnt} = `(Neutral {cnt=~(quote cnt)})
  quote (lhs <+> rhs) {cnt} = `(CommutativeMonoid.(<+>) {cnt=~(quote cnt)} ~(quote lhs) ~(quote rhs))

shiftFin : (offset : Nat) -> Fin n -> Fin (offset + n)
shiftFin Z fin = fin
shiftFin (S offset) fin {n} = rewrite plusSuccRightSucc offset n in shiftFin offset (FS fin)

resize : Expr cnt -> Expr (cnt + offset)
resize (Var idx) = Var (weakenN _ idx)
resize Neutral = Neutral
resize ((<+>) lhs rhs) = (resize lhs) <+> (resize rhs)

shift : Expr cnt -> Expr (offset + cnt)
shift (Var idx) = Var (shiftFin _ idx)
shift Neutral = Neutral
shift ((<+>) lhs rhs) = (shift lhs) <+> (shift rhs)

public export
Parsed : Type
Parsed = (cnt ** (Expr cnt, Vect cnt Raw))

merge : (lhs, rhs : Parsed) -> Parsed
merge (cnt1 ** (expr1, v1)) (cnt2 ** (expr2, v2)) =
  (cnt1 + cnt2 ** (resize expr1 <+> shift expr2, v1 ++ v2))

atom : Raw -> Parsed
atom raw = (S Z ** (Var FZ, [raw]))

export
parse : {binop, neutral : Raw} -> Raw -> Parsed
parse raw@(RApp (RApp func lhs) rhs) {binop} {neutral} =
  if func == binop
    then merge (parse {binop} {neutral} lhs) (parse {binop} {neutral} rhs)
    else atom raw
parse raw {neutral} =
  if raw == neutral
    then (Z ** (Neutral, []))
    else atom raw

remap : Expr n -> Vect n (Fin n') -> Expr n'
remap Neutral _ = Neutral
remap (Var idx) v = Var (idx `index` v)
remap ((<+>) lhs rhs) v = remap lhs v <+> remap rhs v

align : Parsed -> Vect cnt Raw -> Maybe (Expr cnt)
align (_ ** (expr, raws)) raws' = do
  idxs <- for raws $ \raw => do
    idx <- raw `elemIndex` raws'
    pure idx
  pure $ remap expr idxs

canon : Parsed -> Maybe Parsed
canon (_ ** (expr, raws)) =
  let raws' = fromList $ nub $ map (`index` raws) (normalize expr) in
  do
    expr' <- align (_ ** (expr, raws)) raws'
    pure (_ ** (expr', raws'))

public export
data Unified : Type where
  MkUnified : (cnt : Nat) -> (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Vect cnt Raw -> Unified

export
unify : Parsed -> Parsed -> Either String Unified
unify parsed1 parsed2 = do
  let Just (cnt1 ** (expr1, v1)) = canon parsed1
    | Nothing => Left "Encountered a bug (ref: canon1)"
  let Just (cnt2 ** (expr2, v2)) = canon parsed2
    | Nothing => Left "Encountered a bug (ref: canon2)"

  let Yes prfCnt = decEq cnt1 cnt2
    | No _ => Left "The expressions have different numbers of variables"
  let expr1 = replace prfCnt expr1
  let v1 = replace prfCnt v1

  let Just expr2 = align (_ ** (expr2, v2)) v1
    | Nothing => Left "The expresssions have different variables"

  let Yes prfNF = decEq (normalize expr1) (normalize expr2)
    | No _ => Left "The expressions have different normal forms"

  Right $ MkUnified _ expr1 expr2 prfNF v1
