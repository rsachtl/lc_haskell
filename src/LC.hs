import Control.Monad

data E =  N Int |
          F Int E |
          A E E deriving (Show, Eq)

free :: E -> Int -> Bool
free (N a)   b = a /= b
free (F a e) b = a /= b && free e b
free (A e f) b = free e b || free f b

bound :: E -> Int -> Bool
bound e b = not $ free e b

{-}
fv :: E -> [Int]
fv (N a)   = [a]
fv (F a e) = undefined
fv (A e f) = undefined

bv :: E -> [Int]
bv (N a)   = []
bv (F a e) = [a] ++ (bv e)
bv (A e f) = (bv e) ++ (bv f)

subst :: E -> Int -> Int -> Maybe E
subst (N a)   a c = Just $ N c
subst (N a)   b c = Just $ N b
subst (F a e) b c = undefined
subst (A e f) b c = undefined

substE :: E -> Int -> E -> E
substE = undefined

apply :: E -> E
apply (A (F a e) x) = undefined
apply e = undefined
-}
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
