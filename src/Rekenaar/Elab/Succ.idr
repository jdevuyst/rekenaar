module Rekenaar.Elab.Succ

import Data.Vect
import Language.Reflection.Utils

-- pruviloj
import Pruviloj.Core

import Rekenaar.Reflect.Utils

%default covering -- TODO: make tactic total
%access private
%language ElabReflection

findSucc_ : {binop, neutral, succ : Raw} -> TTName -> Raw -> Maybe (Raw, Raw)
findSucc_ var raw {binop} {neutral} {succ} = do
    let Nothing = parseApp succ 1 raw
      | Just [x] => if isNeutral x
                      then Nothing
                      else Just (x, Var var)
    [lhs, rhs] <- parseApp binop 2 raw
    rec lhs (\lhs' => [lhs', rhs]) <|> rec rhs (\rhs' => [lhs, rhs'])
  where
    rec : Raw -> (Raw -> Vect 2 Raw) -> Maybe (Raw, Raw)
    rec term wrap = do
      (x, term') <- findSucc_ {binop} {neutral} {succ} var term
      Just (x, Vect.foldl1 RApp (binop :: wrap term'))
    isNeutral : Raw -> Bool
    isNeutral = isJust . parseApp neutral 0

findSucc : {ty, binop, neutral, succ : Raw} -> Raw -> Elab (Raw, Raw)
findSucc raw {ty} {binop} {neutral} {succ} = do
  var <- gensym "findSuccVar"
  let Just (x, f) = findSucc_ {binop} {neutral} {succ} var raw
    | Nothing => fail [TextPart "Could not find a match for"
                      ,RawPart succ]
  pure (x, RBind var (Lam {a=Raw} ty) f)

repeatUntilFail' : Elab ty -> Elab (List ty)
repeatUntilFail' tactic {ty} = helper []
  where
    helper : List ty -> Elab (List ty)
    helper xs = do
      Just x <- (Just <$> tactic) <|> pure Nothing
        | Nothing => pure xs
      helper (x :: xs)

export
unSucc : {ty, binop, neutral, succ, rewriteRule : Raw} -> {rewriteRuleTerms : Raw -> (Raw, Raw)} -> Elab (List TTName)
unSucc {ty} {binop} {neutral} {succ} {rewriteRule} {rewriteRuleTerms} = do
    repeatUntilFail' (helper id <|> helper flip)
  where
    helper : ({a, b : Type} -> (a -> a -> b) -> (a -> a -> b)) -> Elab TTName
    helper proj = do
      goal <- goalType
      let Just (lhs, rhs) = parseEq goal
        | Nothing => fail [TextPart "Failed to parse (=) type in goal type"
                          ,RawPart goal]

      let (term, otherTerm) = proj MkPair lhs rhs
      (x, f) <- findSucc {ty} {binop} {neutral} {succ} term

      var <- gensym "unSuccVar"
      let (l, r) = proj MkPair (RApp f (Var var)) otherTerm
      let replaceTerm = the Raw `(replace
        {a=~ty}
        {x=~(fst $ rewriteRuleTerms x)}
        {y=~(snd $ rewriteRuleTerms x)}
        {P=~(RBind var (Lam {a=Raw} ty) `((=) {A=~ty} {B=~ty} ~l ~r))}
        ~(RApp rewriteRule x))

      [newHole] <- apply replaceTerm [False]
        | xs => fail (TextPart "Unexpected number of holes" :: map NamePart xs)
      focus newHole
      pure newHole
