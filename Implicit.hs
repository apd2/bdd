{-# LANGUAGE ImplicitParams, FlexibleContexts #-}
module Implicit where

import Data.Bits

import qualified LogicClasses as C

t, b :: (C.Boolean c a, ?m :: c) => a
t = C.topOp ?m
b = C.botOp ?m

(.|), (.&), (.->), xnor, xor, or, and, imp :: (C.Boolean c a, ?m :: c) => a -> a -> a
(.|)  = C.orOp ?m
(.&)  = C.andOp ?m
(.->) = C.impOp ?m
xor   = C.xorOp ?m
xnor  = C.xnorOp ?m
and   = C.andOp ?m
or    = C.orOp ?m
imp   = C.impOp ?m

infixl 6 .&
infixl 5 .|
infixr 1 .-> 

(<.>) = ($)
infix 2 <.>

nt :: (C.Boolean c a, ?m :: c) => a -> a
nt = C.notOp ?m

exists, forall :: (C.QBF c v a, ?m :: c) => v -> a -> a
exists vs x = C.exists ?m vs x 
forall vs x = C.forall ?m vs x

varAtIndex :: (C.VarDecl c v, ?m :: c) => Int -> v
varAtIndex = C.varAtIndex ?m

conj, disj :: (C.Boolean c a, ?m :: c) => [a] -> a
conj = C.conjOp ?m
disj = C.disjOp ?m

swap :: (C.Shiftable c v a, ?m :: c) => v -> v -> a -> a
swap  v1 v2 x    = C.swap  ?m v1 v2 x
shift :: (C.Shiftable c v a, ?m :: c) => Int -> v -> v -> a -> a
shift sz v1 v2 x = C.shift ?m sz v1 v2 x

sat :: (C.Satisfiable c v a s r, ?m :: c) => a -> s
sat = C.sat ?m

satOne :: (C.Satisfiable c v a s r, ?m :: c) => a -> Maybe r
satOne = C.satOne ?m

extract :: (C.Satisfiable c v a s r, ?m :: c) => v -> r -> r
extract = C.extract ?m

expand :: (C.Satisfiable c v a s r, ?m :: c) => [v] -> s -> [[r]]
expand = C.expand ?m

expandOne :: (C.Satisfiable c v a s r, ?m :: c) => v -> s -> [r]
expandOne = C.expandOne ?m

oneSat :: (C.Satisfiable c v a s r, ?m :: c) => v -> a -> Maybe r
oneSat = C.oneSat ?m

eqRaw :: (C.EqRaw c v a r, ?m :: c) => v -> r -> a
eqRaw = C.eqRaw ?m

oneCube :: (C.Cubeable c v a, ?m :: c) => v -> a -> Maybe a
oneCube = C.oneCube ?m

allCubes :: (C.Cubeable c v a, ?m :: c) => v -> a -> [a]
allCubes = C.allCubes ?m

oneSatAndCube :: (C.Satisfiable c v a s [Bool], C.BoolOp c v a, ?m :: c) => v -> a -> Maybe ([Bool], a)
oneSatAndCube = C.oneSatAndCube ?m

(<+>) :: (C.Variable c v, ?m :: c) => v -> v -> v
(<+>) = C.vplus ?m

vplus :: (C.Variable c v, ?m :: c) => v -> v -> v
vplus = C.vplus ?m

vzero :: (C.Variable c v, ?m :: c) => v 
vzero = C.vzero ?m

vconcat :: (C.Variable c v, ?m :: c) => [v] -> v
vconcat = C.vconcat ?m

cube :: (C.Boolean c a, ?m :: c) => [a] -> [Bool] -> a
cube = C.cube ?m

eqConst :: (Bits b, C.EqConst c v a, ?m :: c) => v -> b -> a
eqConst = C.eqConst ?m

eqConstBE :: (Bits b, C.EqConst c v a, ?m :: c) => v -> b -> a
eqConstBE = C.eqConstBE ?m

eqConstLE :: (Bits b, C.EqConst c v a, ?m :: c) => v -> b -> a
eqConstLE = C.eqConstLE ?m

eqVars :: (C.BoolOp c v a, ?m :: c) => v -> v -> a
eqVars = C.eqVars ?m

compVar :: (C.BoolOp c v a, ?m :: c) => v -> [a]
compVar = C.compVar ?m

andAbs, xorAbs, faImp, faXnor :: (C.CUDDLike c v a, ?m :: c) => v -> a -> a -> a
andAbs = C.andAbs ?m
xorAbs = C.xorAbs ?m
faImp  = C.faImp ?m
faXnor = C.faXnor ?m

liCompaction :: (C.CUDDLike c v a, ?m :: c) => a -> a -> a
liCompaction = C.liCompaction ?m

largestCube :: (C.CUDDLike c v a, ?m :: c) => a -> a
largestCube = C.largestCube ?m

makePrime :: (C.CUDDLike c v a, ?m :: c) => a -> a -> a
makePrime = C.makePrime ?m

supportIndices :: (C.CUDDLike c v a, ?m :: c) => a -> [Int]
supportIndices = C.supportIndices ?m

project :: (C.CUDDLike c v a, C.VarDecl c v, ?m :: c) => [Int] -> a -> a
project  = C.project ?m

primeImplicant :: (C.CUDDLike c v a, ?m :: c) => a -> a
primeImplicant = C.primeImplicant ?m

primeCover :: (C.CUDDLike c v a, ?m :: c) => a -> [a]
primeCover = C.primeCover ?m

leq :: (C.CUDDLike c v a, ?m ::c) => a -> a -> Bool
leq = C.leq ?m

varMap :: (C.Mappable c v a, ?m :: c) => a -> a
varMap = C.varMap ?m

intersects :: (C.CUDDLike c v a, ?m ::c) => a -> a -> Bool
intersects = C.intersects ?m
