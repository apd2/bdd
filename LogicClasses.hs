{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleContexts #-}

module LogicClasses (
    Variable(..),
    Shiftable(..),
    Mappable(..),
    Satisfiable(..),
    EqRaw(..),
    Boolean(..),
    QBF(..),
    AllOps(..),
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

--Variables
class Variable c v | c -> v where
    vzero :: c -> v
    vplus :: c -> v -> v -> v
    vconcat :: c -> [v] -> v

--Operations
--Have to have stupid names because of clashes with prelude names
class Boolean c a | c -> a where
    iteOp                                            :: c -> a -> a -> a -> a
    andOp, orOp, xorOp, xnorOp, impOp, nandOp, norOp :: c -> a -> a -> a
    nandOp c x y                                     = notOp c $ andOp c x y
    norOp c x y                                      = notOp c $ orOp c x y
    xnorOp c x y                                     = notOp c $ xorOp c x y
    impOp c x y                                      = orOp c (notOp c x) y
    orOp c x y                                       = notOp c $ andOp c (notOp c x) (notOp c y)
    andOp c x y                                      = notOp c $ orOp c (notOp c x) (notOp c y)
    xorOp c x y                                      = andOp c (orOp c x y) (notOp c (andOp c x y))
    notOp                                            :: c -> a -> a
    topOp, botOp                                     :: c -> a
    topOp c                                          = notOp c (botOp c)
    botOp c                                          = notOp c (topOp c)
    conjOp, disjOp                                   :: c -> [a] -> a
    conjOp d xs                                      = foldl (andOp d) (topOp d) xs
    disjOp d xs                                      = foldl (orOp d) (botOp d) xs

cube :: (Boolean c a) => c -> [a] -> [Bool] -> a
cube m nodes phase = conjOp m $ zipWith (alt id (notOp m)) phase nodes

class Boolean c a => QBF c v a | c -> v, c -> a where
    exists, forall                    :: c -> v -> a -> a

--Renaming
class Shiftable c v a | c -> v, c -> a where
    shift :: c -> Int -> v -> v -> a -> a
    swap  :: c -> v -> v -> a -> a

class Mappable c v a | c -> v, c -> a where
    varMap :: c -> a -> a

--Minterm and cube extraction
class Cubeable c v a where
	oneCube     :: c -> v -> a -> Maybe a
	allCubes    :: c -> v -> a -> [a]
	oneMinterm  :: c -> v -> a -> Maybe a
	allMinterms :: c -> v -> a -> [a]

--Satisfiability
class Satisfiable c v a s r | c -> v, c -> a, c -> s, c -> r where
    sat       :: c -> a -> s
    satOne    :: c -> a -> Maybe r
    extract   :: c -> v -> r -> r
    expand    :: c -> [v] -> s -> [[r]]
    expandOne :: c -> v -> s -> [r]
    oneSat    :: c -> v -> a -> Maybe r

oneSatAndCube :: (Satisfiable c v a s [Bool], BoolOp c v a) => c -> v -> a -> Maybe ([Bool], a)
oneSatAndCube c v a = do
    res <- oneSat c v a
    return (res, cube c (compVar c v) res)

--Serialization
class Serialisable c a where 
    toStr   :: (MonadError String me) => c -> a -> me String
    fromStr :: (MonadError String me) => c -> String -> me a

--Constant equality
class EqRaw c v a r | c -> v, c -> a, c -> r where
    eqRaw :: c -> v -> r -> a

class EqConst c v a where
	eqConstLE :: (Bits b) => c -> v -> b -> a
	eqConstBE :: (Bits b) => c -> v -> b -> a
	eqConst   :: (Bits b) => c -> v -> b -> a

eqVars :: (BoolOp c v a) => c -> v -> v -> a
eqVars c l r = conjOp c $ zipWith (xnorOp c) (compVar c l) (compVar c r)

--It makes more sense to have compVar return another abstract type that represents compiled vars and use these in the compiler and for EqConst
class QBF c v a => BoolOp c v a | c -> a, c -> v where
    compVar :: c -> v -> [a]
    varCube :: c -> v -> a

class (Variable c v, Shiftable c v a, QBF c v a, Eq a, BoolOp c v a, EqConst c v a) => AllOps c v a
class (AllOps c v a, Satisfiable c v a s r) => AllAndSat c v a s r

--Stuff specific to BDD libraries
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

