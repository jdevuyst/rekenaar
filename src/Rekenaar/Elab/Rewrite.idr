module Rekenaar.Elab.Rewrite

import Language.Reflection.Utils

-- contrib
import Data.Fuel
import Pruviloj.Core

%access private
%default total

collectTypes : Raw -> List Raw
collectTypes (RBind _ (Pi ty _) t) = ty :: collectTypes t
collectTypes t = [t]

findConflict : {ty : Raw} -> {default id make : Raw -> Raw} -> Raw -> Raw -> Elab $ Maybe (Raw -> Raw, Raw, Raw)
findConflict raw1@(RApp f1 arg1) raw2@(RApp f2 arg2) {ty} {make} = do
  res1 <- findConflict {ty} {make=make . flip RApp arg1} f1 f2
  res2 <- findConflict {ty} {make=make . RApp f1} arg1 arg2
  case (res1, res2) of
    (Nothing, Nothing) => pure Nothing
    (Just t, Nothing) => pure $ Just t
    (Nothing, Just t) => pure $ Just t
    (Just (make', raw1', raw2'), Just _) => do
      env <- getEnv
      ty1 <- forget $ snd !(check env raw1)
      ty1' <- forget $ snd !(check env raw1')
      if ty1 == ty || ty1' /= ty
        then pure $ Just (make, raw1, raw2)
        else pure $ Just (make', raw1', raw2')
findConflict raw1 raw2 {make} = pure $
  if raw1 == raw2 then Nothing else Just (make, raw1, raw2)

replaceFirstConflict : {ty : Raw} -> Raw -> Raw -> Raw -> Elab (Raw, Raw, List TTName)
replaceFirstConflict value argTy retTy {ty} = do
  Just (make, argArg, retArg) <- findConflict {ty} argTy retTy
    | Nothing => pure (value, argTy, [])

  (_, ty) <- check !getEnv argArg
  ty <- forget ty

  holeName <- gensym "rewriterHole"
  let holeType = the Raw `((=) {A=~ty} {B=~ty} ~argArg ~retArg)
  claim holeName holeType

  let p = RBind (UN "updateVar")
                (Lam ty)
                (make (Var (UN "updateVar")))
  (x, x') <- check !getEnv p
  let updateCall = the Raw `(replace {a=~ty} {x=~argArg} {y=~retArg} {P=~p} ~(Var holeName) ~value)

  pure (RBind holeName (Hole holeType) updateCall, make retArg, [holeName])

replaceConflicts : {default forever fuel : Fuel} -> {ty : Raw} -> Raw -> Raw -> Raw -> Elab (Raw, Raw, List TTName)
replaceConflicts _ _ _ {fuel=Dry} = fail [TextPart "replaceConflicts ran out of fuel"]
replaceConflicts value argTy retTy {fuel=More fuel} {ty} = do
  (newValue, newArgTy, holes) <- replaceFirstConflict {ty} value argTy retTy
  if isCons holes
    then do
      (newValue', newArgTy', holes') <- replaceConflicts {fuel} {ty} newValue newArgTy retTy
      pure (newValue', newArgTy', holes ++ holes')
    else pure (newValue, newArgTy, holes)

export covering
rewriter_ : {ty : Raw}  -> Elab (List TTName)
rewriter_ {ty} = do
  let tys = collectTypes !goalType
  for_ (take (length tys `minus` 2) tys) $ \_ => intro'

  RBind _ (Pi argTy _) retTy <- goalType
    | goalTy => fail [TextPart "rewriter requires a function type for goal", RawPart goalTy]

  arg <- gensym "rewriterArg"
  intro arg

  (arg', _, holes) <- replaceConflicts {ty} (Var arg) argTy retTy
  exact arg'

  pure holes

export covering
rewriter : {ty : Raw} -> Elab () -> Elab ()
rewriter tactic {ty} = do
  rewriter_ {ty} `andThen` tactic
  pure ()
