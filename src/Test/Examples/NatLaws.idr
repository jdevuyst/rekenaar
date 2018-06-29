module Test.Examples.NatLaws

-- contrib
import Interfaces.Verified

-- pruviloj
import Pruviloj.Core

import Rekenaar.Elab.Monoid

%default total
%access private
%language ElabReflection

natLaw : Elab ()
natLaw = do
  intros
  refl {ty=`(Nat)} {tc=`(PlusNatMonoidV)} {binop=`(plus)} {neutral=`(Z)}

plusZeroLeftNeutral : (r : Nat) -> 0 + r = r
plusZeroLeftNeutral = %runElab natLaw

plusZeroRightNeutral : (l : Nat) -> l + 0 = l
plusZeroRightNeutral = %runElab natLaw

plusAssociative : (l : Nat) -> (c : Nat) -> (r : Nat) -> l + (c + r) = (l + c) + r
plusAssociative = %runElab natLaw
