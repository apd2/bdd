{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}

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

import LogicClasses
import Cudd
import Util
import BDDCommon

type VarData = VarDataG DdNode

instance Boolean DdManager DdNode where
	iteOp         = cuddBddIte
	xnorOp        = cuddBddXnor
	xorOp         = cuddBddXor
	andOp         = cuddBddAnd
	orOp          = cuddBddOr
	impOp         = cuddBddImp
	notOp         = cuddNot
	topOp         = cuddReadOne
	botOp         = cuddReadLogicZero
        eqOp _        = (==)

instance QBF DdManager VarData DdNode where
	exists m vs n = cuddBddExistAbstract m n (varsCube vs)
	forall m vs n = cuddBddUnivAbstract  m n (varsCube vs)

instance AllOps DdManager VarData DdNode
    
instance BoolOp DdManager VarData DdNode where
    compVar m    = variables

instance Variable DdManager VarData where
    vplus m (VarData vl il cl sil) (VarData vr ir cr sir) = VarData (vl++vr) (il ++ ir) (andOp m cl cr) (merge (<) sil sir)
    vminus m (VarData vl il cl sil) v@(VarData vr ir cr sir) = VarData undefined undefined (exists m v cl) undefined
    vzero m = VarData [] [] (topOp m) []
    vconcat m list = foldl (vplus m) (vzero m) list

instance Shiftable DdManager VarData DdNode where
    shift m sz vl vr n = cuddBddPermute m n (makePermutArray sz (indices vl) (indices vr))
    swap  m vl vr n = cuddBddSwapVariables m n (variables vl) (variables vr)

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

instance Satisfiable DdManager VarData DdNode [[SatBit]] [Bool] where
    sat           = cuddAllSat
    satOne m a    = map (==One) `fmap` cuddOneSat m a 
    extract m v   = indexes (sortedInds v) 
    expand m v    = expandSat (map indices v)
    expandOne m v = comb . map (indexes $ sortedInds v)
    oneSat m v n  = do
        res <- cuddOneSat m n
        let x = map (==One) res
        return $ indexesDef False (sortedInds v) x

instance EqRaw DdManager VarData DdNode [Bool] where
    eqRaw m v r = LogicClasses.cube m (variables v) r

instance Serialisable DdManager DdNode where
    toStr = bddToString
    fromStr = bddFromString

instance Cubeable DdManager VarData DdNode where
	oneCube c v a = cube c (compVar c v) `liftM` oneSat c v a 
	allCubes m vd = map (cube m $ compVar m vd) . expandOne m vd . sat m

instance EqConst DdManager VarData DdNode where
	eqConstLE m vars e = cube m (variables vars) (bitsToBoolArrLe e)
	eqConstBE m vars e = cube m (variables vars) (bitsToBoolArrBe (length $ variables vars) e)
	eqConst = eqConstBE

instance CUDDLike DdManager VarData DdNode where
    andAbs m vd x y    = cuddBddAndAbstract m x y (varsCube vd)
    xorAbs m vd x y    = cuddBddXorExistAbstract m x y (varsCube vd)
    liCompaction       = cuddBddLICompaction
    largestCube        = snd .* cuddLargestCube
    makePrime          = cuddBddMakePrime
    supportIndices m n = map snd $ filter fst $ zip (cuddSupportIndex m n) [0..]
    leq                = cuddBddLeq 

instance VarDecl DdManager VarData where
    varAtIndex m i = indicesToVarData m [i] 

indicesToVarData :: DdManager -> [Int] -> VarData 
indicesToVarData m inds = VarData vars inds (conjOp m vars) (sort inds)
    where
    vars = map (cuddBddIthVar m) inds

