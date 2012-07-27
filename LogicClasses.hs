{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts #-}

module LogicClasses (
    UnOpType,
    BinOpType,
    TernOpType,
    ListOpType,
    Variable(..),
    Shiftable(..),
    Mappable(..),
    Satisfiable(..),
    EqRaw(..),
    BOp(..),
    AllOps(..),
    AllAndSat(..),
    Serialisable(..),
    Cubeable(..),
    oneSatAndCube,
    cube,
    EqConst(..),
    eqVars,
    BoolOp(..),
    CUDDLike(..)
    ) where

import Control.Monad.Error
import Data.List
import Data.Bits 

import Util

--Data and operator types
type UnOpType   a = a -> a
type BinOpType  a = a -> a -> a
type TernOpType a = a -> a -> a -> a
type ListOpType a = [a] -> a

class Variable c v | c -> v where
    vzero :: c -> v
    vplus :: c -> v -> v -> v
    vconcat :: c -> [v] -> v

class Shiftable c v a | c -> v, c -> a where
    shift :: c -> Int -> v -> v -> a -> a
    swap  :: c -> v -> v -> a -> a

class Mappable c v a | c -> v, c -> a where
    varMap :: c -> a -> a

class Satisfiable c v a s r | c -> v, c -> a, c -> s, c -> r where
    sat       :: c -> a -> s
    satOne    :: c -> a -> Maybe r
    extract   :: c -> v -> r -> r
    expand    :: c -> [v] -> s -> [[r]]
    expandOne :: c -> v -> s -> [r]
    oneSat    :: c -> v -> a -> Maybe r

class EqRaw c v a r | c -> v, c -> a, c -> r where
    eqRaw :: c -> v -> r -> a

class BOp c v a | c -> a, c -> v where
    iteOp                             :: c -> TernOpType a
    xnorOp, andOp, orOp, xorOp, impOp :: c -> BinOpType a
    notOp                             :: c -> UnOpType a
    topOp, botOp                      :: c -> a
    exists, forall                    :: c -> v -> UnOpType a
    conjOp, disjOp :: BOp c v a => c -> [a] -> a
    conjOp d xs = foldl (andOp d) (topOp d) xs
    disjOp d xs = foldl (orOp d)  (botOp d) xs

class (Variable c v, Shiftable c v a, BOp c v a, Eq a, BoolOp c v a, EqConst c v a) => AllOps c v a
class (AllOps c v a, Satisfiable c v a s r) => AllAndSat c v a s r

class Serialisable c a where 
    toStr   :: (MonadError String me) => c -> a -> me String
    fromStr :: (MonadError String me) => c -> String -> me a

class Cubeable c v a where
	oneCube     :: c -> v -> a -> Maybe a
	allCubes    :: c -> v -> a -> [a]
	oneMinterm  :: c -> v -> a -> Maybe a
	allMinterms :: c -> v -> a -> [a]

oneSatAndCube :: (Satisfiable c v a s [Bool], BoolOp c v a) => c -> v -> a -> Maybe ([Bool], a)
oneSatAndCube c v a = do
    res <- oneSat c v a
    return (res, cube c (compVar c v) res)

cube :: (BOp c v a) => c -> [a] -> [Bool] -> a
cube m nodes phase = conjOp m $ zipWith (alt id (notOp m)) phase nodes

class EqConst c v a where
	eqConstLE :: (Bits b) => c -> v -> b -> a
	eqConstBE :: (Bits b) => c -> v -> b -> a
	eqConst   :: (Bits b) => c -> v -> b -> a

eqVars :: (BoolOp c v a) => c -> v -> v -> a
eqVars c l r = conjOp c $ zipWith (xnorOp c) (compVar c l) (compVar c r)

--It makes more sense to have compVar return another abstract type that represents compiled vars and use these in the compiler and for EqConst

--Basic operator definitions
class BOp c v a => BoolOp c v a | c -> a, c -> v where
    compVar :: c -> v -> [a]
    varCube :: c -> v -> a

class AllOps c v a => CUDDLike c v a where
    andAbs, xorAbs, faImp, faXnor :: c -> v -> a -> a -> a

    andAbs m v x y = exists m v $ andOp m x y
    xorAbs m v x y = exists m v $ xorOp m x y
    faImp  m v x y = notOp m $ andAbs m v x (notOp m y)
    faXnor m v x y = notOp m $ xorAbs m v x y

    liCompaction :: c -> a -> a -> a

    largestCube :: c -> a -> a
    makePrime :: c -> a -> a -> a

    supportIndices :: c -> a -> [Int]

    primeImplicant :: c -> a -> a
    primeImplicant m x = makePrime m (largestCube m x) x

    primeCover :: c -> a -> [a]
    primeCover m y = unfoldr func y
        where
        func x 
            | x == botOp m = Nothing
            | otherwise = Just (ret, st)
                where
                ret = makePrime m (largestCube m x) y
                st  = andOp m (notOp m ret) x

    leq :: c -> a -> a -> Bool
    leq m l r = (impOp m l r) == topOp m

    intersects :: c -> a -> a -> Bool
    intersects m l r = not $ leq m l (notOp m r)

