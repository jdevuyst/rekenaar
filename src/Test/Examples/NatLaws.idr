module Test.Examples.NatLaws

-- contrib
import Interfaces.Verified

-- pruviloj
import Pruviloj.Core

import Rekenaar.Elab.CommutativeMonoid

%default total
%access private
%language ElabReflection

natLaw : Elab ()
natLaw = do
  intros
  refl {ty=`(Nat)} {tc=`(PlusNatCommMonoidV)} {binop=`(plus)} {neutral=`(Z)}

plusZeroLeftNeutral : (r : Nat) -> 0 + r = r
plusZeroLeftNeutral = %runElab natLaw

plusZeroRightNeutral : (l : Nat) -> l + 0 = l
plusZeroRightNeutral = %runElab natLaw

plusAssociative : (l : Nat) -> (c : Nat) -> (r : Nat) -> l + (c + r) = (l + c) + r
plusAssociative = %runElab natLaw

plusCommutative : (l : Nat) -> (r : Nat) -> l + r = r + l
plusCommutative = %runElab natLaw

contrivedExample : (a, b, c, d : Nat) -> a + (Z + (b + Z + d) + Z) + (c + c) = (d + b) + ((Z + c + a) + c)
contrivedExample = %runElab natLaw
