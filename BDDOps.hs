{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances, FlexibleContexts #-}

module BDDOps (
    VarData,
    VarDataG(..)
    ) where

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.List
import Control.Monad

import System.IO.Unsafe
import Control.Monad.Error
import Data.Maybe
import System.Directory

import LogicClasses
import qualified Cudd.Cudd as C
import Cudd.Cudd (DDNode, DDManager, SatBit(..))
import Cudd.File
import Util
import BDDCommon

type VarData = VarDataG DDNode

instance Boolean DDManager DDNode where
    iteOp         = C.bIte
    xnorOp        = C.bXnor
    xorOp         = C.bXor
    andOp         = C.bAnd
    orOp          = C.bOr
    impOp m l r   = C.bOr m (C.bNot m l) r
    notOp         = C.bNot
    topOp         = C.readOne
    botOp         = C.readLogicZero
    eqOp _        = (==)

instance QBF DDManager VarData DDNode where
	exists m vs n = C.bExists m n (varsCube vs)
	forall m vs n = C.bForall  m n (varsCube vs)

instance AllOps DDManager VarData DDNode
    
instance BoolOp DDManager VarData DDNode where
    compVar m    = variables

instance Variable DDManager VarData where
    vplus m (VarData vl il cl sil) (VarData vr ir cr sir) = VarData (vl++vr) (il ++ ir) (andOp m cl cr) (merge (<) sil sir)
    vminus m (VarData vl il cl sil) v@(VarData vr ir cr sir) = VarData undefined undefined (exists m v cl) undefined
    vzero m = VarData [] [] (topOp m) []
    vconcat m list = foldl (vplus m) (vzero m) list

instance Shiftable DDManager VarData DDNode where
    shift m sz vl vr n = C.permute m n (makePermutArray sz (indices vl) (indices vr))
    swap  m vl vr n = C.swapVariables m n (variables vl) (variables vr)

--Converts the result of calling sat on CUDD to a satisfying list of bools where dont care conditions
--are expanded out
comb :: [[SatBit]] -> [[Bool]]
comb xs = concat $ map f xs
    where
        f x        = allComb $ map g x
        g Zero     = [False]
        g One      = [True]
        g DontCare = [False, True]

expandSat :: [[Int]] -> [[SatBit]] -> [[[Bool]]]
expandSat vars sat = transpose $ map funcy vars
    where
    combList = IntSet.toAscList $ IntSet.unions (map IntSet.fromList vars)
    revMap   = IntMap.fromList $ zip combList [0..] 
    sats     = comb $ nub $ map (indexes combList) sat
    trans    = transpose sats
    funcy vs = transpose $ indexes (map ((IntMap.!) revMap) vs) trans

instance Satisfiable DDManager VarData DDNode [[SatBit]] [Bool] where
    sat           = C.allSat
    satOne m a    = map (==One) `fmap` C.oneSat m a 
    extract m v   = indexes (sortedInds v) 
    expand m v    = expandSat (map indices v)
    expandOne m v = comb . map (indexes $ sortedInds v)
    oneSat m v n  = do
        res <- C.oneSat m n
        let x = map (==One) res
        return $ indexesDef False (sortedInds v) x

instance EqRaw DDManager VarData DDNode [Bool] where
    eqRaw m v r = LogicClasses.cube m (variables v) r

instance Serialisable DDManager DDNode where
    toStr = bddToString
    fromStr = bddFromString

instance Cubeable DDManager VarData DDNode where
	oneCube c v a = cube c (compVar c v) `liftM` oneSat c v a 
	allCubes m vd = map (cube m $ compVar m vd) . expandOne m vd . sat m

instance EqConst DDManager VarData DDNode where
	eqConstLE m vars e = cube m (variables vars) (bitsToBoolArrLe e)
	eqConstBE m vars e = cube m (variables vars) (bitsToBoolArrBe (length $ variables vars) e)
	eqConst = eqConstBE

instance CUDDLike DDManager VarData DDNode where
    andAbs m vd x y    = C.andAbstract m x y (varsCube vd)
    xorAbs m vd x y    = C.xorExistAbstract m x y (varsCube vd)
    liCompaction       = C.liCompaction
    largestCube        = snd .* C.largestCube
    makePrime          = C.makePrime
    supportIndices m n = map snd $ filter fst $ zip (C.supportIndex m n) [0..]
    leq                = C.lEq 

instance VarDecl DDManager VarData where
    varAtIndex m i = indicesToVarData m [i] 

indicesToVarData :: DDManager -> [Int] -> VarData 
indicesToVarData m inds = VarData vars inds (conjOp m vars) (sort inds)
    where
    vars = map (C.ithVar m) inds

-- BDD from string via file
bddFromString :: MonadError String me => DDManager -> String -> me DDNode
bddFromString m str = unsafePerformIO $ 
    catchError (do let fname = "_fromString.bdd"
                   writeFile fname str
                   node <- cuddBddLoad m DddmpVarMatchauxids [] [] DddmpModeText fname
                   removeFile fname
                   return $ return $ fromJust node)
               (return . throwError . show)

-- Extremely ugly and unsafe way to convert BDD to String via file
bddToString :: (MonadError String me) => DDManager -> DDNode -> me String
bddToString m node = unsafePerformIO $ 
    catchError (do let fname = show (C.ddNodeToInt node) ++ ".bdd"
                   ret <- cuddBddStore m fname node [] DddmpModeText DddmpVarids fname
                   --putStrLn $ "ret = " ++ (show ret)
                   if ret == True
                           then do str <- readFile fname
                                   removeFile fname
                                   return $ return str
                           else return $ throwError $ "Failed to serialise BDD (status: " ++ show ret ++ ")")
               (return . throwError . show)

