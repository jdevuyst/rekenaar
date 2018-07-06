module Test.Examples.NatLaws

import Rekenaar

%default total
%access private
%language ElabReflection

plusZeroLeftNeutral : (r : Nat) -> 0 + r = r
plusZeroLeftNeutral = %runElab natPlusRefl

plusZeroRightNeutral : (l : Nat) -> l + 0 = l
plusZeroRightNeutral = %runElab natPlusRefl

plusAssociative : (l, c, r : Nat) -> l + (c + r) = (l + c) + r
plusAssociative = %runElab natPlusRefl

plusCommutative : (l, r : Nat) -> l + r = r + l
plusCommutative = %runElab natPlusRefl

contrivedExample : (a, b, c, d : Nat) -> a + (Z + (b + Z + d) + Z) + (c + c) = (d + b) + ((Z + c + a) + c)
contrivedExample = %runElab natPlusRefl
