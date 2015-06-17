module Comb where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import LC as LC
import LCDB as DB


-- Map to all free vars in a given expression a number
-- how far they will be above scope in DB.
-- Example:  \x. (\y. x y u) z
--   u and z are free, thus getting numbers higher than
--   the current scope in DB, but they are different, too, 
--   and thus every free u will be +1 above current scope,
--   whereas each free z will be the next value above and
--   therefore will be +2 above current scope.
varsToDB :: LC.E -> Int -> Set Int -> Map Int Int -> (Int,Map Int Int)
varsToDB (LC.N x) overscope bvs vars = if (Set.member x bvs)
    then (overscope, vars)
    else case (Map.lookup x vars) of 
        (Just y) -> (overscope, vars) 
        Nothing  -> let 
                overscope' = overscope+1
                vars' = Map.insert x overscope' vars
            in (overscope', vars')
varsToDB (LC.A e f) overscope bvs vars = varsToDB f oscope' bvs vars'
    where
        (oscope',vars') = varsToDB e overscope bvs vars
varsToDB (LC.F a f) overscope bvs vars = varsToDB f overscope bvs' vars
    where
        bvs' = Set.union bvs (Set.singleton a)

-- Convert a naive expression to a DB expression, tracking
-- current scope-depth (curScope), the names of the vars currently bound
-- in order of their bounding (bvs) and a mapping how high a 
-- free var will be above current scope (overScopes).     
structToDB :: LC.E -> Int -> [Int]-> Map Int Int -> DB.E
structToDB (LC.N x) curScope bvs overScopes = case (Map.lookup x overScopes) of
    (Just y) -> DB.V $ curScope + y
    Nothing  -> case (List.elemIndices x bvs) of
        []  -> error $ "encountered unknown variable"
        bs  -> DB.V $ curScope - (last bs)    
structToDB (LC.A e f) curScope bvs overScopes = 
    DB.A (structToDB e curScope bvs overScopes) 
            (structToDB f curScope bvs overScopes)
structToDB (LC.F a f) curScope bvs overScopes = 
    DB.L $ structToDB f (curScope+1) (bvs++[a]) overScopes

-- Convert a naive expr. to a DB expression.
convertLCtoDB :: LC.E -> DB.E
convertLCtoDB e = structToDB e 0 [] overscopes
    where
        (_,overscopes) = varsToDB e 0 Set.empty Map.empty 


structFromDB :: DB.E -> Int -> Int -> LC.E
structFromDB (DB.V x) scope max = if (x <= scope)
    then LC.N $ scope - x + 1
    else LC.N $ max + (x - scope)
structFromDB (DB.A e f) scope max = 
    LC.A (structFromDB e scope max) (structFromDB f scope max)
structFromDB (DB.L e) scope max = LC.F scope' e'
    where
        scope' = scope + 1
        e' = structFromDB e scope' max 



convertDBtoLC :: DB.E -> LC.E
convertDBtoLC e = structFromDB e 0 $ DB.maxScope e 0

{- Test expressions -}
testLC_1 :: LC.E
testLC_1 = LC.F 1 $ LC.F 2 $ LC.A (LC.A (LC.N 3) (LC.N 1)) (LC.F 4 $ LC.A (LC.N 4) (LC.N 1))  

testLC_2 :: LC.E
testLC_2 = LC.F 1 $ LC.A (LC.N 5) (LC.N 1)

testLC_3 :: LC.E
testLC_3 = LC.A testLC_1 testLC_2 

testDB_1 :: DB.E
testDB_1 = DB.A (DB.L (DB.L (DB.A (DB.A (DB.V 3) (DB.V 2)) (DB.L (DB.A (DB.V 1) (DB.V 3)))))) (DB.L (DB.A (DB.V 3) (DB.V 1)))


convNum :: Int -> DB.E
convNum = convertLCtoDB . fromNum

convSuc :: Int -> Maybe Int
convSuc n = asNum resultLC
    where
        aLC = LC.A fS $ fromNum n 
        aDB = convertLCtoDB aLC
        resultDB = DB.reduceFull aDB 
        resultLC = convertDBtoLC resultDB

convRes :: Int -> ((LC.E,DB.E),(LC.E,DB.E))
convRes n = ((aLC, aDB),(resultLC,resultDB))
    where
        aLC = LC.A fS $ fromNum n 
        aDB = convertLCtoDB aLC
        resultDB = DB.reduceFull aDB     
        resultLC = convertDBtoLC resultDB

fS_DB :: DB.E
fS_DB = convertLCtoDB LC.fS

fS_DB' :: DB.E
fS_DB' = convertLCtoDB LC.fS'

fS_DB'' :: DB.E 
fS_DB'' = convertLCtoDB LC.fS''