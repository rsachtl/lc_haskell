module LCDB where

import Control.Monad
import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Maybe as Maybe

data E  =  V Int -- Variable
         | L E   -- Abstractor
         | A E E -- Applicator
            deriving (Eq, Show)

data SE =  SV Int
         | SL SE
         | SA SE SE
         | B    -- Box for Replacement
            deriving (Eq, Show)

maxScope :: E -> Int -> Int
maxScope (V x)   n = n
maxScope (A e f) n = max (maxScope e n) (maxScope f n)
maxScope (L e)   n = maxScope e (n+1)

-- mark all vars in the epression that are bound by the lambda
-- at distance d as Boxes 
box :: E -> Int -> SE
box (V n) d
    | n == d = B
    | True   = SV n
box (L e) d = SL $ box e (d+1)
box (A e f) d = SA (box e d) (box f d) 

-- decrease all free vars by one
decFree :: SE -> Int -> SE
decFree (SV n) scope 
    | n > scope = SV $ n-1
    | otherwise = SV n
decFree (SA e f) scope = SA (decFree e scope) (decFree f scope)
decFree (SL e) scope = SL $ decFree e $ scope+1 
decFree B _ = B

-- increase all free vars by outer-scope
incFree :: E -> Int -> Int -> E 
incFree (V n) oscope iscope 
    | n > iscope = V $ n+oscope
    | otherwise = V n
incFree (A e f) oscope iscope = 
    A (incFree e oscope iscope) (incFree f oscope iscope)
incFree (L e) oscope iscope = L $ incFree e oscope $ iscope+1

-- Replace all boxes in the SE by a given expression r.
-- Free variables in r are increased accordingly at each 
-- point of replacement.
replace :: SE -> E -> Int -> E
replace (SV n) r scope = V n
replace (SA e f) r scope = A (replace e r scope) (replace f r scope)
replace (SL e) r scope = L $ replace e r $ scope+1
replace B r scope = incFree r scope 0

-- perform beta-reduction
reduce :: E -> E
reduce (A (L m) n) = replace dec n 0
    where
        bx  = box m 1
        dec = decFree bx 0         
reduce e = e

-- check if two expressions are alpha-equivalent
alphaEq :: E -> E -> Bool
alphaEq = (==)



-- perform beta-reduction as long as possible
reduceFull :: E -> E
reduceFull e =
    let 
        e' = reduce e
    in
        if (alphaEq e e')
            then e
            else reduceFull e'

testE1 :: E
testE1 = (L $ A (A (V 4) (V 2)) (L $ A (V 1) (V 3)))

testE2 :: E
testE2 = A (L testE1) (L $ A (V 5) (V 1))


          