module LC where

import Control.Monad
import Data.Set as Set
import Data.Map as Map
import Data.List as List
import Data.Maybe as Maybe

data E =  N Int |                   -- A name/variable
          F Int E |                 -- A Function, read \x.e
          A E E deriving (Show, Eq) -- An Application (e1 e2)

-- True if b is free in a given expression
free :: E -> Int -> Bool
free (N a)   b = a /= b
free (F a e) b = a /= b && free e b
free (A e f) b = free e b || free f b

-- True if b is bound in e
bound :: E -> Int -> Bool
bound e b = not $ free e b

-- Free variables in a given expression
fv :: E -> Set Int
fv (N a)   = Set.singleton a
fv (F a e) = (fv e) Set.\\ Set.singleton a
fv (A e f) = Set.union (fv e) (fv f)

-- Bound variables in a given expression
bv :: E -> Set Int
bv (N a)   = Set.empty
bv (F a e) = Set.union (bv e) (Set.singleton a)
bv (A e f) = Set.union (bv e) (bv f)

-- get all variables in a given expression
vars :: E -> Set Int
vars e = Set.union (bv e) (fv e)

-- Rename a variable in a given expression
-- Does not rename bound variables 
rename :: E -> Int -> Int -> E
rename (N a) b c 
    | a == b = N c
    | True   = N a
rename (F a e) b c
    | a == b = F a e
    | True   = F a $ rename e b c
rename (A e f) b c = A (rename e b c) (rename f b c)       

-- hange all indices by a given function
-- Does not guarantee not changing bounding
changeIndicesBy :: (Int -> Int) -> E -> E
changeIndicesBy f (N a)   = N $ f a
changeIndicesBy f (F a e) = F (f a) $ changeIndicesBy f e
changeIndicesBy f (A e g) = 
    A (changeIndicesBy f e) (changeIndicesBy f g)


substE :: E -> Int -> E -> E
substE (N a) b r = if (a == b) then r
                               else (N a)
substE (A e f) b r = A (substE e b r) (substE f b r)
substE (F a f) b r = if (a == b)
    then F a f
    else F a' $ substE f' b r
        where
            vR = vars r
            (minR,maxR) = if (vR == Set.empty)
                    then (0,0)
                    else (Set.findMin vR, Set.findMax vR)
            vF = vars f
            (minF,maxF) = if (vF == Set.empty)
                    then (0,0)
                    else (Set.findMin vF, Set.findMax vF)
            fger = minF >= maxR
            rgef = minR >= maxF
            delta = case (minF > 0, maxF > 0, minR > 0, maxR > 0, fger, rgef) of
                (_,_,_,_,True,_) -> 0
                (_,_,_,_,_,True) -> 0
                ( True,    _, True,    _,_,_) -> maxR + 1
                ( True,    _,False, True,_,_) -> maxR + 1
                (False, True, True,    _,_,_) -> maxR + abs minF + 1
                (False,False,False, True,_,_) -> maxR + abs minF + 1
                (False,False,False,False,_,_) -> abs minR + abs minF + 1
                _ -> 0 
            a' = a + delta      
            f' = rename f a a'
             
-- check whether the given expressions are alpha-equivalent
alphaEq :: E -> E -> Bool
alphaEq e f = structEq e f Map.empty

structEq :: E -> E -> Map Int Int -> Bool
structEq (N x) (N y) bvs = case (Map.lookup x bvs) of
    (Just z) -> y == z
    Nothing  -> x == y
structEq (A e1 f1) (A e2 f2) bvs = 
    structEq e1 e2 bvs && structEq f1 f2 bvs
structEq (F a1 e1) (F a2 e2) bvs =
    structEq e1 e2 $ Map.insert a1 a2 bvs 
structEq _ _ _ = False


-- perform one reduction step
apply :: E -> E
apply (A (F a e) x) = substE e a x
apply e = e

reduce :: E -> E
reduce (A e f) = evaluate $ A e' f'
    where
        e' = reduce e
        f' = reduce f
reduce (F a e) = F a $ reduce e
reduce e = e    

reduceFull :: E -> E
reduceFull e =
    let 
        e' = reduce e
    in
        if (alphaEq e e')
            then e
            else reduceFull e'    


-- reduce as long as
evaluate :: E -> E
evaluate e =
    let 
        e' = apply e
    in
        if (alphaEq e e') 
            then e
            else evaluate e'    

asNum :: E -> Maybe Int
asNum (F a (F b e)) = countComp e a b 0
asNum _ = Nothing

countComp :: E -> Int -> Int -> Int -> Maybe Int
countComp (N x) s z n 
    | x == z = Just n
    | True   = Nothing
countComp (A x y) s z n
    | x == (N s) = countComp y s z (n+1)
    | True   = Nothing
countComp x s z n = Nothing


fromNum :: Int -> E
fromNum n = F 1 $ F 2 $ repeatAppl (N 2) (N 1) n

-- Repeat application of a on e n times
repeatAppl :: E -> E -> Int -> E
repeatAppl e a n = iterate (A a) e !! n


asBool :: E -> Maybe Bool
asBool (F a (F b (N x))) 
    | x == a = Just True
    | x == b = Just False
    | True   = Nothing 
asBoolt x = Nothing




fI :: E
fI = F 1 (N 1)

fT :: E
fT = F 1 $ F 2 $ N 1

fF :: E
fF = F 1 $ F 2 $ N 2

fNot :: E
fNot = F 1 $ A (A (N 1) fF) fT

fAnd :: E
fAnd = F 1 $ F 2 $ A (A (N 1) (N 2)) fF

fOr :: E
fOr = F 1 $ F 2 $ A (A (N 1) fT) $ N 2

fS :: E
fS = F 1 $ F 2 $ F 3 $ A (N 2) $ A (A (N 1) (N 2)) $ N 3

fS' :: E
fS' = F 2 $ F 3 $ A (N 2) $ A (A (N 1) (N 2)) $ N 3

fS'' :: E 
fS'' = F 3 $ A (N 2) $ A (A (N 1) (N 2)) $ N 3

fLeq :: E
fLeq = F 1 $ A (A (A (N 1) fF) fNot) fF

fFst :: E
fFst = fT

fSnd :: E
fSnd = fF

isPair :: E -> Bool
isPair (F x (A (A (N y) a) b)) = x == y
isPair x = False

fGenPair :: E
fGenPair = F 1 $ F 2 $ A (A (N 1) (A fS (A (N 1) fT))) $ A (N 1) fT

fMul :: E
fMul = F 1 $ F 2 $ F 3 $ A (N 1) (A (N 2) (N 3))


par :: String -> String
par x 
    | length x > 1 = "("++x++")"
    | otherwise    = x

toStr :: E -> String
toStr (N x)   = show x
toStr (F x e) = "\\" ++ (show x) ++ "." ++ (toStr e)
toStr (A x y) = (par (toStr x)) ++ " " ++ (par (toStr y))

fE = (A (N 1) (A fT fT))