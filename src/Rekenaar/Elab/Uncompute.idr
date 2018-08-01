module Rekenaar.Elab.Uncompute

import Language.Reflection.Utils

-- pruviloj
import Pruviloj.Core

%default covering
%access export

unSucc : {binop, neutral, succ : Raw} -> Raw -> Raw
unSucc {binop} {neutral} {succ} = newTy
  where
    plusOne : Raw
    plusOne = RApp binop (RApp succ neutral)
    newTy : Raw -> Raw
    newTy (RApp f x) =
      RApp
        (if f == succ then plusOne else newTy f)
        (newTy x)
    newTy (RBind n b expr) = RBind n (newTy <$> b) (newTy expr)
    newTy expr = expr

uncompute : (Raw -> Raw) -> Elab TTName
uncompute f = do equiv (f !goalType)
