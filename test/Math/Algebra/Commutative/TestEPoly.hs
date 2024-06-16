{-# LANGUAGE DataKinds #-}

{- |  This module tests the "Math.Algebra.Commutative.EPoly" module.  -}

module Math.Algebra.Commutative.TestEPoly (
    epTestOps, ePolyTests
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


evTestOps               :: Cmp ExponVec -> [PrecText] -> Range Word -> TestOps ExponVec
-- @descVarPTs@ lists more main variables first.
evTestOps evCmp descVarPTs eRange   = TestOps (evShowPrecF evVPTs) evTCheck evGen (cmpEq evCmp)
  where
    evVPTs@(EvVarPTs { nVars })     = evVarPTs descVarPTs evCmp
    evTCheck notes ev   = tCheckBool (showT ev : notes) (evMake (exponsL nVars ev) == ev)
    evVarPow i e    = evMake [if j == i then e else 0 | j <- [0 .. nVars - 1]]
    varPowGen       = liftA2 evVarPow (Gen.int (Range.constant 0 (nVars - 1))) (Gen.word eRange)
    evGen           = foldl' (evPlus nVars) (evVarPow 0 0) <$>
                        Gen.list (Range.linear 0 nVars) varPowGen

epTestOps               :: Ring c -> Cmp ExponVec -> Range Int -> TestOps c ->
                            TestOps ExponVec -> TestOps (EPoly c)
-- ^ @epTestOps cR evCmp sumRange cTA evTA@.
-- The caller tests @cR@ and @evCmp@, including that @evCmp@ gives a total order.
epTestOps cR            = ssTestOps cR.ag

test1                   :: Int -> TestTree
test1 nVars             = testGroup ("EPoly " <> show nVars) testsL
  where
    -- should change to a noncommutative coef ring C with zero divisors, and check indets
    -- commute with it, for non-GroebnerBasis tests:
    sec             = GrRevLexCmp  -- @@@
    (cR, _)         = zzModPW @2_000_003
    cTA             = zpwTestOps @2_000_003
    evCmp           = epEvCmpF nVars sec
    epA@(EPolyOps { epUniv })   = epOps cR nVars evCmp
    UnivL pR (RingTgtXs cToEp xs) epUnivF   = epUniv
    nToT            = cR.fromZ
    nextT b         = cR.plus (cR.times (nToT 1234) b) (nToT 567)
    ts              = take nVars (unfoldr (\b -> Just (b, nextT b)) (nToT 12345))
    epToT           = epUnivF cR (RingTgtXs id ts)
    descVarTs       = take nVars alphaNumVarNames
    descVarPTs      = map (PrecText atomPrec) descVarTs
    useSugar        = UseSugar True     -- @@@
    gbpA@(GBPolyOps { descVarPs, pShowPrec })   =
        epGBPOps evCmp (secIsGraded sec) cR descVarPTs cTA.tSP useSugar
    evTA            = evTestOps evCmp descVarPTs (Range.exponential 1 200_000)
    pTA             = epTestOps cR evCmp (Range.linear 0 10) cTA evTA
    -- @@ improve EPoly GB testing:
    evTSmall        = evTestOps evCmp descVarPTs (Range.linear 1 3)
    pTSmall         = epTestOps cR evCmp (Range.linear 0 3) cTA evTSmall
    gbTestsL        = [groebnerBasisTests gbpA  (listTestOps (Range.linear 0 2) pTSmall)
                        (epCountZeros cR (map cR.fromZ [0 .. 10]) epA) | nVars <= 3]
    reqFlags        =
        RingFlags { commutative = True, noZeroDivisors = True, nzInverses = False }
    
    testsL          = [totalOrderTests evTA (==) (IsNontrivial True) evCmp,
                        ringTests pTA (IsNontrivial True) reqFlags pR,
                        ringHomomTests (Just "Ring Homomorphism from C") cTA cR pTA.tEq pR
                            cToEp,
                        testOnce "xs" $ map ((.t) . pShowPrec) descVarPs === descVarTs,
                        ringHomomTests (Just "Ring Homomorphism to C") pTA pR cTA.tEq cR epToT,
                        singleTest "C -> T" $ sameFun1TR cTA cTA.tEq (epToT . cToEp) id,
                        testOnce "xs ->" $ listTestEq cTA (map epToT xs) ts,
                        parseTest pTA (zzGensRingParse pR (varParse descVarTs descVarPs))]
                        ++ gbTestsL

ePolyTests              :: TestTree
ePolyTests              = testGroup "EPoly" $ map test1 [1, 2, 3, 5, 9, 14, 20]
