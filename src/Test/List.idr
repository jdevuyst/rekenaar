module Test.List

import Rekenaar

%default total
%access private
%language ElabReflection

appendNilLeftNeutral : (r : List a) -> [] ++ r = r
appendNilLeftNeutral = %runElab listRefl

appendNilRightNeutral : (l : List a) -> l ++ [] = l
appendNilRightNeutral = %runElab listRefl

appendAssociative : (l, c, r : List a) -> l ++ c ++ r = (l ++ c) ++ r
appendAssociative = %runElab listRefl

prependSingletonConsElement : (l, r : List a) -> (x : a) -> (l ++ [x]) ++ r = l ++ (x::r)
prependSingletonConsElement = %runElab listRefl
