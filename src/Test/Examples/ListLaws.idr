module Test.Examples.ListLaws

-- contrib
import Interfaces.Verified

-- pruviloj
import Pruviloj.Core

import Rekenaar.Elab.Monoid

%default total
%access private
%language ElabReflection

ListMonoidV : (a : Type) -> VerifiedMonoid (List a)
ListMonoidV = %runElab (do intros; search)

listLaw : Elab ()
listLaw = do
  a <- gensym "a"
  intro a
  intros
  refl {ty=`(List ~(Var a))} {tc=`(ListMonoidV ~(Var a))} {binop=`(List.(++) {a=~(Var a)})} {neutral=`(List.Nil {elem=~(Var a)})}

appendNilLeftNeutral : (a : Type) -> (r : List a) -> [] ++ r = r
appendNilLeftNeutral = %runElab listLaw

appendNilRightNeutral : (a : Type) -> (l : List a) -> l ++ [] = l
appendNilRightNeutral = %runElab listLaw

appendAssociative : (a : Type) -> (l : List a) -> (c : List a) -> (r : List a) -> l ++ c ++ r = (l ++ c) ++ r
appendAssociative = %runElab listLaw
