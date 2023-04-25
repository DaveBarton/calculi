{-# LANGUAGE DataKinds #-}

{- |  This module tests the "EPoly" module.  -}

module Math.Algebra.Commutative.TestEPoly (
    epTestOps, testEPoly
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Category.Category
import Math.Algebra.Commutative.Field.ZModPW
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.EPoly

import Math.Algebra.General.TestAlgebra
import Math.Algebra.Commutative.Field.TestZModPW
import Math.Algebra.General.TestSparseSum
import Math.Algebra.Commutative.TestGroebnerBasis

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.List (unfoldr)


evTestOps               :: Cmp ExponVec -> [String] -> Range Word -> TestOps ExponVec
-- @descVarSs@ lists more main variables first, and each @varS@ has precedence > '^'.
evTestOps evCmp descVarSs eRange    = TestOps (evShowPrecF evSs) evTCheck evGen (cmpEq evCmp)
  where
    evSs@(EvVarSs { nVars })    = evVarSs descVarSs evCmp
    evTCheck notes ev   = tCheckBool (show ev : notes) (evMake (exponsL nVars ev) == ev)
    evVarPow i e    = evMake [if j == i then e else 0 | j <- [0 .. nVars - 1]]
    varPowGen       = liftA2 evVarPow (Gen.int (Range.constant 0 (nVars - 1))) (Gen.word eRange)
    evGen           = foldl' (evPlus nVars) (evVarPow 0 0) <$>
                        Gen.list (Range.linear 0 nVars) varPowGen

epTestOps               :: Ring c -> Cmp ExponVec -> Range Int -> TestOps c ->
                            TestOps ExponVec -> TestOps (EPoly c)
-- ^ @epTestOps cR evCmp sumRange cT evT@
-- The caller tests @cR@ and @evCmp@, including that @evCmp@ gives a total order.
epTestOps cR            = ssTestOps cR.ag

test1                   :: Int -> IO Bool
-- 1 <= nVars <= 26
test1 nVars             = checkGroup ("EPoly " ++ show nVars) props
  where
    -- should change to a noncommutative coef ring C with zero divisors, and check indets
    -- commute with it, for non-GroebnerBasis tests:
    sec             = GrRevLexCmp  -- @@@
    (cR, _)         = zzModPW @2_000_003
    cT              = zpwTestOps @2_000_003
    evCmp           = epEvCmpF nVars sec
    epA@(EPolyOps { epUniv })   = epOps cR nVars evCmp
    UnivL pR (RingTgtXs cToEp xs) epUnivF   = epUniv
    nToT            = cR.fromZ
    nextT b         = cR.plus (cR.times (nToT 1234) b) (nToT 567)
    ts              = take nVars (unfoldr (\b -> Just (b, nextT b)) (nToT 12345))
    epToT           = epUnivF cR (RingTgtXs id ts)
    descVarSs       = map (: []) (take nVars ['a' .. 'z'])
    useSugar        = True  -- @@@
    gbpA@(GBPolyOps { descVarPs, pShow })   =
        epGBPOps evCmp (secIsGraded sec) cR descVarSs (const cT.tShow) useSugar
    evT             = evTestOps evCmp descVarSs (Range.exponential 1 200_000)
    pT              = epTestOps cR evCmp (Range.linear 0 10) cT evT
    -- @@ improve EPoly GB testing:
    evTSmall        = evTestOps evCmp descVarSs (Range.linear 1 3)
    pTSmall         = epTestOps cR evCmp (Range.linear 0 3) cT evTSmall
    gbProps         = if nVars > 3 then [] else
                        groebnerBasisProps gbpA  (listTestOps (Range.linear 0 2) pTSmall)
                            (epCountZeros cR (map cR.fromZ [0 .. 10]) epA)
    
    props           = totalOrderProps evT (==) evCmp
                        ++ ringProps pT (eiBit IsCommutativeRing) pR
                        ++ ringHomomProps cT cR pT.tEq pR cToEp
                        ++ [("xs", propertyOnce $ map pShow descVarPs === descVarSs)]
                        ++ ringHomomProps pT pR cT.tEq cR epToT
                        ++ [("C -> T", property $ sameFun1TR cT cT.tEq (epToT . cToEp) id),
                            ("xs ->", propertyOnce $ listTestEq cT (map epToT xs) ts),
                            readsProp pT (polynomReads pR (zip descVarSs descVarPs))]
                        ++ gbProps

testEPoly               :: IO Bool
testEPoly               = checkAll $ map test1 [1, 2, 3, 5, 9, 14, 20]
