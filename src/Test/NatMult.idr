module Test.NatMult

import Data.Fin

import Rekenaar

%default total
%access private
%language ElabReflection

%freeze mult

multOneLeftNeutral : (r : Nat) -> 1 * r = r
multOneLeftNeutral = %runElab natMultRefl

multOneRightNeutral : (l : Nat) -> l * 1 = l
multOneRightNeutral = %runElab natMultRefl

multAssociative : (l, c, r : Nat) -> l * (c * r) = l * c * r
multAssociative = %runElab natMultRefl

multCommutative : (l, r : Nat) -> l * r = r * l
multCommutative = %runElab natMultRefl

multCommutativeRewrite : (l, r : Nat) -> Fin (l * r) -> Fin (r * l)
multCommutativeRewrite l r fin =
  rewrite the (r * l = l * r) (%runElab natMultRefl) in fin
