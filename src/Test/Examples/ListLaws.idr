module Test.Examples.ListLaws

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
