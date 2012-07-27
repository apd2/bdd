{-#LANGUAGE TypeFamilies, EmptyDataDecls, ImplicitParams #-}

module TypeFamily where

import Cudd

type family C a
type family V a
type family A a
type family S a
type family R a

data CUDDBDD 

data VarData = VarData {variables :: [DdNode], indices :: [Int], varsCube :: DdNode, sortedInds :: [Int]}

type instance C CUDDBDD = DdManager
type instance V CUDDBDD = VarData
type instance A CUDDBDD = DdNode
type instance S CUDDBDD = [[SatBit]]
type instance R CUDDBDD = [Bool]

type UnOpType   a = a -> a
type BinOpType  a = a -> a -> a
type TernOpType a = a -> a -> a -> a

class BOp i where
    iteOp                             :: i -> C i -> TernOpType (A i)
    xnorOp, andOp, orOp, xorOp, impOp :: i -> C i -> BinOpType (A i)
    notOp                             :: i -> C i -> UnOpType (A i)
    topOp, botOp                      :: i -> C i -> A i
    exists, forall                    :: i -> C i -> V i -> UnOpType (A i)

class Satisfiable i where
    sat       :: i -> C i -> A i -> S i
    satOne    :: i -> C i -> A i -> Maybe (R i)
    extract   :: i -> C i -> V i -> R i -> R i
    expand    :: i -> C i -> [V i] -> S i -> [[R i]]
    expandOne :: i -> C i -> V i -> S i -> [R i]
    oneSat    :: i -> C i -> V i -> A i -> Maybe (R i)

instance BOp CUDDBDD where
	iteOp  i        = cuddBddIte
	xnorOp i        = cuddBddXnor
	xorOp  i        = cuddBddXor
	andOp  i        = cuddBddAnd
	orOp   i        = cuddBddOr
	impOp  i        = cuddBddImp
	notOp  i        = cuddNot
	topOp  i        = cuddReadOne
	botOp  i        = cuddReadLogicZero
	exists i m vs n = cuddBddExistAbstract m n (varsCube vs)
	forall i m vs n = cuddBddUnivAbstract  m n (varsCube vs)

instance Satisfiable CUDDBDD where
    sat       i     = cuddAllSat
    satOne    i m a = map (==One) `fmap` cuddOneSat m a 
    extract   i     = undefined
    expand    i     = undefined
    expandOne i     = undefined
    oneSat    i     = undefined

test :: (BOp i, Satisfiable i, ?inst :: i) => C i -> A i -> A i -> S i
test c x y = sat ?inst c (andOp ?inst c x y)

{-
test :: (?inst :: i, ?m :: C i, BOp i) => V i -> A i -> A i
test = exists ?inst ?m
-}
