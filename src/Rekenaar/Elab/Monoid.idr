module Rekenaar.Elab.Monoid

import Data.Fin
import Data.Vect

-- contrib
import Interfaces.Verified

-- pruviloj
import Pruviloj.Core

import Rekenaar.Infer.Monoid
import Rekenaar.Reflect.Monoid

%default total
%access private
%language ElabReflection

elabEq_ : (ty, tc : Raw) -> (lhs, rhs : Expr cnt) -> normalize lhs = normalize rhs -> Vect cnt Raw -> Elab Raw
elabEq_ ty tc lhs rhs prf atoms {cnt} = do
  let cnt' = the Raw $ quote cnt
  let lhs' = the Raw $ quote lhs
  let rhs' = the Raw $ quote rhs
  let prf' = the Raw $ quote prf

  let solution = the Raw `(Monoid.solve' ~ty ~tc ~cnt' ~lhs' ~rhs' ~prf')

  let atoms' = rawVect atoms ty
  let env' = the Raw `(MkEnv {ty=~ty} {m=~tc} {cnt=~cnt'} ~atoms')

  pure $ RApp solution env'

mPart : String -> {binop, neutral : TTName} -> Raw -> ErrorReportPart
mPart title raw {binop} {neutral} =
  let (cnt ** (expr, atoms)) = parse {binop} {neutral} raw in

  let binopReport = SubReport [TextPart "`", NamePart binop, TextPart "`"] in
  let nf = intersperse binopReport $ map RawPart $ map (`index` atoms) (normalize expr) in

  SubReport [TextPart title
            ,SubReport [TextPart "Raw:"
                       , RawPart raw]
            ,SubReport [TextPart "Number of arguments:"
                       , TextPart $ show $ length atoms]
            ,SubReport $ (TextPart "Normal form:") :: nf]

elabEq : {binop, neutral : TTName} -> {tc : Raw} -> (lhs, rhs : Raw) -> Elab Raw
elabEq lhs rhs {binop} {neutral} {tc} = do
  let parsed1 = parse {binop} {neutral} lhs
  let parsed2 = parse {binop} {neutral} rhs

  let Right (MkUnified cnt expr1 expr2 prfNF atoms) = unify parsed1 parsed2
    | Left msg => fail [TextPart "Unification failure"
                       ,mPart "LHS" {binop} {neutral} lhs
                       ,mPart "RHS" {binop} {neutral} rhs
                       ,SubReport [TextPart "Binary operation:"
                                  ,NamePart binop]
                       ,SubReport [TextPart "Neutral element:"
                                  ,NamePart neutral]
                       ,SubReport [TextPart $ "Reason: " ++ msg]]

  ty <- getTTType lhs
  ty' <- forget ty
  -- TODO: Resolve interface implementation here

  elabEq_ ty' tc expr1 expr2 prfNF atoms

refl : {binop, neutral : TTName} -> {tc : Raw} -> Elab ()
refl {binop} {neutral} {tc} = do
  g <- goalType
  let Just (lhs, rhs) = parseEq g
    | Nothing => fail [TextPart "Could not parse (=) goal type"
                      ,RawPart g]
  prf <- elabEq {binop} {neutral} {tc} lhs rhs
  exact prf

anExample : (x : Nat) -> x + x = (x + Z) + x
anExample x = %runElab (refl {binop=`{plus}} {neutral=`{Z}} {tc=`(PlusNatMonoidV)})
