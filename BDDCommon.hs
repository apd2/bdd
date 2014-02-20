{-#LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module BDDCommon (
    makePermutArray,
    VarDataG(..)
    ) where

import Control.DeepSeq
import Data.Foldable
import Data.Traversable
import Data.Array hiding (indices)

makePermutArray :: Int -> [Int] -> [Int] -> [Int]
makePermutArray size x y = elems $ accumArray (flip const) 0 (0, size-1) ascList
    where
    ascList = [(i, i) | i <- [0..size-1]] ++ zip x y 

data VarDataG nt = VarData {variables :: [nt], indices :: [Int], varsCube :: nt, sortedInds :: [Int]} deriving (Functor, Foldable, Traversable)
