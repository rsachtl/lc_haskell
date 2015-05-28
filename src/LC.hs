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

-- substitute a given variable in an expression with another expression
-- TODO: use more efficient renaming of variables
substE :: E -> Int -> E -> E
substE (N a) b r 
    | a == b = r
    | a /= b = (N a)
substE (A x y) b r = A (substE x b r) (substE y b r)
substE (F a f) b r 
    | a == b = F a f
    | a /= b = F y (substE f' b r')
        where 
            y  = (+1) . Set.findMax $ vars f
            r' = changeIndicesBy (+y) r
            f' = rename f a y     

alphaEq :: E -> E -> Bool
alphaEq e1 e2 = case (varPairStructEq e1 e2 Map.empty Set.empty Set.empty) of
    (Just m) -> renamingPossible m
    Nothing  -> False

varPairStructEq :: E -> E -> Map Int Int -> Set Int -> Set Int -> Maybe (Map Int Int)
varPairStructEq (N a)   (N b)   m v1 v2 = case (Set.member a v1, Set.member b v2) of
    (True, True)  -> Just m
    (False,False) -> case (Map.lookup a m) of
        (Just x) -> if (x == b)
            then Just $ m
            else Nothing
        Nothing  -> Just $ Map.insert a b m
    _ -> Nothing
varPairStructEq (F a e) (F b f) m v1 v2 = 
    varPairStructEq e f m (Set.insert a v1) (Set.insert b v2)
varPairStructEq (A e f) (A g h) m v1 v2 =
    let 
        pairsLeft  = (varPairStructEq e g m v1 v2)
        pairsRight = (varPairStructEq f h m v1 v2)  
        mLeft      = fromJust pairsLeft
        mRight     = fromJust pairsRight  
        interPairs = Map.intersection mLeft mRight
        es         = Map.elems interPairs
        unique     = length es == (Set.size $ Set.fromList es) 
    in     
        if (isJust pairsLeft && isJust pairsRight && unique)
            then Just $ Map.union mLeft mRight
            else Nothing    
varPairStructEq _ _ _ _ _ = Nothing    

unifyVarPairs :: Maybe (Map Int Int) -> Maybe (Map Int Int) -> Maybe (Map Int Int)
unityVarPairs (Just m1) (Just m2) = 
    let
        unionLeft  = Map.union m1 m2
        unionRight = Map.union m2 m1
        diff       = Map.difference unionRight unionLeft
    in 
        if (diff == Map.empty)
            then Just unionLeft
            else Nothing    
unifyVarPairs m1 m2 = Nothing 

renamingPossible :: Map Int Int -> Bool
renamingPossible m = 
    let
        es       = Map.elems m
    in 
        length es == (Set.size $ Set.fromList es)    

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


par :: String -> String
par x 
    | length x > 1 = "("++x++")"
    | otherwise    = x

toStr :: E -> String
toStr (N x)   = show x
toStr (F x e) = "\\" ++ (show x) ++ "." ++ (toStr e)
toStr (A x y) = (par (toStr x)) ++ " " ++ (par (toStr y))

fE = (A (N 1) (A fT fT))