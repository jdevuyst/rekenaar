module Rekenaar.Reflect.Utils

import Data.Vect

-- contrib
import Language.Reflection.Utils

-- pruviloj
import Pruviloj.Core

%default total
%access export

implementation Quotable (Fin k) Raw where
  quotedTy {k} = `(Fin ~(quote k))
  quote FZ {k=S k'} = `(FZ {k=~(quote k')})
  quote (FS x) {k=S k'} = `(FS {k=~(quote k')} ~(quote x))

implementation (Quotable a Raw, Quotable b Raw) => Quotable ((=) {A=a} {B=b} x y) Raw where
  quotedTy {a} {b} {x} {y} = `((=) {A=~(quotedTy {a})} {B=~(quotedTy {a=b})} ~(quote x) ~(quote y))
  quote Refl {a} {x} = `(Refl {A=~(quotedTy {a})} {x=~(quote x)})

rawVect : Vect cnt Raw -> Raw -> Raw
rawVect [] ty = `(Vect.Nil {elem=~ty})
rawVect (x::xs) ty {cnt = S cnt'} = `(Vect.(::) {elem=~ty} {len=~(quote cnt')} ~x ~(rawVect xs ty))

parseApp : Raw -> (argc : Nat) -> Raw -> Maybe (Vect argc Raw)
parseApp fun argc raw = map reverse $ helper argc raw
  where
    helper : (argc : Nat) -> Raw -> Maybe (Vect argc Raw)
    helper Z fun' = if fun == fun' then Just [] else Nothing
    helper (S argc) (RApp f arg) = map (arg ::) (helper argc f)
    helper (S _) _ = Nothing

parseEq : Raw -> Maybe (Raw, Raw)
parseEq = map proj . parseApp (Var `{(=)}) 4
  where
    proj : Vect 4 Raw -> (Raw, Raw)
    proj v = (2 `index` v, 3 `index` v)
