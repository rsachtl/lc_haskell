import Control.Monad
import Data.Set 

data E =  N Int |
          F Int E |
          A E E deriving (Show, Eq)

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
fv (N a)   = singleton a
fv (F a e) = (fv e) \\ singleton a
fv (A e f) = union (fv e) (fv f)

-- Bound variables in a given expression
bv :: E -> Set Int
bv (N a)   = empty
bv (F a e) = union (bv e) (singleton a)
bv (A e f) = union (bv e) (bv f)

-- get all variables in a given expression
vars :: E -> Set Int
vars e = union (bv e) (fv e)

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
            y  = (+1) . findMax $ vars f
            r' = changeIndicesBy (+y) r
            f' = rename f a y     


apply :: E -> E
apply (A (F a e) x) = undefined
apply e = undefined



asNum :: E -> Maybe Int
asNum (F a (F b e)) = countComp e a b 0
asNum (N x) = Nothing


countComp :: E -> Int -> Int -> Int -> Maybe Int
countComp (N x) s z n 
    | x == z = Just n
    | True   = Nothing
countComp (A x y) s z n
    | x == (N s) = countComp y s z (n+1)
    | True   = Nothing
countComp x s z n = Nothing

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
