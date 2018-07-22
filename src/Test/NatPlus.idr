module Test.NatPlus

import Data.Fin

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

plusCommutativeRewrite : (l, r : Nat) -> Fin (l + r) -> Fin (r + l)
plusCommutativeRewrite l r fin =
  rewrite the (r + l = l + r) (%runElab natPlusRefl) in fin

plusOneSucc : (r : Nat) -> 1 + r = S r
plusOneSucc = %runElab natPlusRefl

plusOneSucc' : (r : Nat) -> r + 1 = S r
plusOneSucc' = %runElab natPlusRefl

plusSuccRightSucc : (l, r : Nat) -> S (l + r) = l + (S r)
plusSuccRightSucc = %runElab natPlusRefl

plusSuccLeftSucc : (l, r : Nat) -> S (l + r) = (S l) + r
plusSuccLeftSucc = %runElab natPlusRefl

succSuccPlusTwo : (n : Nat) -> S (S n) = n + 2
succSuccPlusTwo = %runElab natPlusRefl

contrivedExample : (a, b, c, d : Nat) -> a + (4 + (b + 3 + d) + Z) + (c + c) = (d + b) + ((2 + 3 + c + a) + 2 + c)
contrivedExample = %runElab natPlusRefl
