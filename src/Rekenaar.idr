module Rekenaar

-- contrib
import Interfaces.Verified

-- pruviloj
import Pruviloj.Core

import Rekenaar.Reflect.Utils
import public Rekenaar.Elab.Monoid
import public Rekenaar.Elab.CommutativeMonoid
import public Rekenaar.Elab.Uncompute

%default total
%access public export
%language ElabReflection

ListMonoidV : VerifiedMonoid (List elem)
ListMonoidV = %runElab (do intros; search)

listRefl : Elab ()
listRefl = do
  intros
  compute
  -- TODO: replace all (x :: xs) by [x] ++ xs (where xs ≠ Nil)
  g <- goalType
  let Just (l, _) = parseEq g
    | Nothing => fail [TextPart "Could not parse (=) of lists", RawPart g]
  (_, listTyTT) <- check !getEnv l
  listTy <- forget listTyTT
  let Just [elemTy] = parseApp (Var `{List}) 1 listTy
    | Nothing => fail [TextPart "LHS of (=) is not a list type", RawPart listTy]
  Monoid.refl {ty=listTy} {tc=`(ListMonoidV {elem=~elemTy})} {binop=`(List.(++) {a=~elemTy})} {neutral=`(List.Nil {elem=~elemTy})}

covering
natPlusRefl : Elab ()
natPlusRefl = do
  intros
  compute
  uncompute $ unSucc {binop=`(plus)} {neutral=`(Z)} {succ=`(S)}
  CommutativeMonoid.refl {ty=`(Nat)} {tc=`(PlusNatCommMonoidV)} {binop=`(plus)} {neutral=`(Z)}

-- TODO: add natMultRefl, zzPlusRefl, zzMultRefl
