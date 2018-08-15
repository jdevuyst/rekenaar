module Test.Misc

import Data.Vect

-- contrib
import Test.Unit

import Rekenaar.Elab.CommutativeMonoid

%default total
%access private

[showNF] Show (CommutativeMonoid.NormalForm n) where
  show xs {n} = show $ map (show . (finToInteger {n})) xs

[eqNF] Eq (CommutativeMonoid.NormalForm n) where
  (==) xs ys = show @{showNF} xs == show @{showNF} ys

covering export
commutativeMonoid_sortNF_test : IO ()
commutativeMonoid_sortNF_test = do
    let input = toList $ range {len=7}
    let testCases = permutate input ++ ([input ++ input ++ reverse input])
    runTests $
      (flip map) testCases $ \xs => do
        assertEquals @{eqNF} @{showNF} (sort xs) (sortNF xs)
  where
    covering
    permutate : Eq ty => List ty -> List (List ty)
    permutate [] = [[]]
    permutate l = do
      h <- l
      t <- permutate $ filter (\x => x /= h) l
      pure (h::t)
