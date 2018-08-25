module Test.Rewrite

import Data.Fin
import Data.Vect
import Language.Reflection.Utils

-- contrib
import Pruviloj.Core

import Rekenaar.Reflect.Utils
import Rekenaar.Elab.Rewrite

%default total
%access private
%language ElabReflection

symRefl : Elab ()
symRefl = do
  goal <- goalType
  let Just (lhs, rhs) = parseEq goal
    | _ => debugMessage [TextPart "Cannot parse (=)", RawPart goal]
  let (RApp (RApp _ x) y) = lhs
    | _ => debugMessage [TextPart "Cannot parse lhs", RawPart lhs]
  fill `(plusCommutative ~x ~y)
  solve

rewriteFin : (l, r : Nat) -> Fin (l + r) -> Fin (r + l)
rewriteFin = %runElab (rewriter {ty=`(Nat)} symRefl)

rewriteVect : (l, r : Nat) -> Vect (l + r) Int -> Vect (r + l) Int
rewriteVect = %runElab (rewriter {ty=`(Nat)} symRefl)

rewriteVectOfFin : (l, r, n : Nat) -> Vect n (Fin $ l + r) -> Vect n (Fin $ r + l)
rewriteVectOfFin = %runElab (rewriter {ty=`(Nat)} symRefl)

rewriteVectOfFin' : (l, r, l', r' : Nat) -> Vect (l + r) (Fin $ l' + r') -> Vect (r + l) (Fin $ r' + l')
rewriteVectOfFin' = %runElab (rewriter {ty=`(Nat)} symRefl)

-- TODO: Add support for functions
-- rewriteFun : (l, r, l', r' : Nat) -> (Fin (l + r) -> Fin (l' + r')) -> Fin (r + l) -> Fin (r' + l')
