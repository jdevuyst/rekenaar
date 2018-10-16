module Rekenaar.Elab.CommutativeMonoid

import public Data.Fin
import public Data.Vect

-- contrib
import Interfaces.Verified

-- pruviloj
import Pruviloj.Core

import public Rekenaar.Infer.Common
import public Rekenaar.Infer.CommutativeMonoid
import Rekenaar.Reflect.CommutativeMonoid

%default total
%access private
%language ElabReflection

elabEq_ : (ty, tc : Raw) -> (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Vect cnt Raw -> Elab Raw
elabEq_ ty tc lhs rhs prf atoms {cnt} = do
  let cnt' = the Raw $ quote cnt
  let lhs' = the Raw $ quote lhs
  let rhs' = the Raw $ quote rhs
  let prf' = the Raw $ quote prf

  let solution = the Raw `(CommutativeMonoid.solve @{~tc} {ty=~ty} {cnt=~cnt'} ~lhs' ~rhs' ~prf')

  let atoms' = rawVect atoms ty
  let env' = the Raw `(MkEnv {ty=~ty} {cnt=~cnt'} ~atoms')

  pure $ RApp solution env'

mPart : String -> {binop, neutral : Raw} -> Raw -> ErrorReportPart
mPart title raw {binop} {neutral} =
  let (cnt ** (expr, atoms)) = parse {binop} {neutral} raw in

  let binopReport = SubReport [TextPart "`", RawPart binop, TextPart "`"] in
  let nf = intersperse binopReport $ map RawPart $ map (`index` atoms) (normalize expr) in

  SubReport [TextPart title
            ,SubReport [TextPart "Raw:"
                       , RawPart raw]
            ,SubReport [TextPart "Number of arguments:"
                       , TextPart $ show $ length atoms]
            ,SubReport $ (TextPart "Normal form:") :: nf]

elabEq : {ty, tc, binop, neutral : Raw} -> (lhs, rhs : Raw) -> Elab Raw
elabEq lhs rhs {ty} {tc} {binop} {neutral} = do
  let parsed1 = parse {binop} {neutral} lhs
  let parsed2 = parse {binop} {neutral} rhs

  let Right (MkUnified cnt expr1 expr2 prfNF atoms) = unify parsed1 parsed2
    | Left msg => fail [TextPart "Unification failure"
                       ,mPart "LHS" {binop} {neutral} lhs
                       ,mPart "RHS" {binop} {neutral} rhs
                       ,SubReport [TextPart "Binary operation:"
                                  ,RawPart binop]
                       ,SubReport [TextPart "Neutral element:"
                                  ,RawPart neutral]
                       ,SubReport [TextPart $ "Reason: " ++ msg]]

  elabEq_ ty tc expr1 expr2 prfNF atoms

export
refl : {ty, tc, binop, neutral : Raw} -> Elab ()
refl {ty} {tc} {binop} {neutral} = do
  g <- goalType
  let Just (lhs, rhs) = parseEq g
    | Nothing => fail [TextPart "Could not parse (=) goal type"
                      ,RawPart g]
  prf <- elabEq {ty} {tc} {binop} {neutral} lhs rhs
  exact prf
