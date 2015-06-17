module Comb where

import Data.Map as Map
import Data.Set as Set
import Data.List as List
import LC as LC
import LCDB as LCDB


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
structToDB :: LC.E -> Int -> [Int]-> Map Int Int -> LCDB.E
structToDB (LC.N x) curScope bvs overScopes = case (Map.lookup x overScopes) of
    (Just y) -> LCDB.V $ curScope + y
    Nothing  -> case (List.elemIndices x bvs) of
        []  -> error $ "encountered unknown variable"
        bs  -> LCDB.V $ curScope - (last bs)    
structToDB (LC.A e f) curScope bvs overScopes = 
    LCDB.A (structToDB e curScope bvs overScopes) 
            (structToDB f curScope bvs overScopes)
structToDB (LC.F a f) curScope bvs overScopes = 
    LCDB.L $ structToDB f (curScope+1) (bvs++[a]) overScopes

-- Convert a naive expr. to a DB expression.
convertLCtoLCDB :: LC.E -> LCDB.E
convertLCtoLCDB e = structToDB e 0 [] overscopes
    where
        (_,overscopes) = varsToDB e 0 Set.empty Map.empty 



{- Test expressions -}
testLC_1 :: LC.E
testLC_1 = LC.F 1 $ LC.F 2 $ LC.A (LC.A (LC.N 3) (LC.N 1)) (LC.F 4 $ LC.A (LC.N 4) (LC.N 1))  

testLC_2 :: LC.E
testLC_2 = LC.F 1 $ LC.A (LC.N 5) (LC.N 1)

testLC_3 :: LC.E
testLC_3 = LC.A testLC_1 testLC_2 

