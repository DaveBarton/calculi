{-# LANGUAGE DataKinds #-}

{- |  This module tests the "EPoly" module.  -}

module Math.Algebra.Commutative.TestEPoly (
    testEPoly
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Category.Category
import Math.Algebra.Commutative.Field.ZModP32
import Math.Algebra.Commutative.GroebnerBasis (GBPolyOps(..))
import Math.Algebra.Commutative.EPoly

import Math.Algebra.General.TestAlgebra
import Math.Algebra.Commutative.Field.TestZModP32

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Monad (liftM2, zipWithM_)
import Data.List (unfoldr)


test1                   :: Int -> IO Bool
-- 1 <= nVars <= 26
test1 nVars             = checkGroup ("EPoly " ++ show nVars) props
  where
    -- should change to a noncommutative coef ring C with zero divisors, and check indets
    -- commute with it:
    (cRing, _)      = zzModPW @2_000_003
    (cSG@(cShow, cGen), cTestEq)    = zpwTestOps @2_000_003
    epru            = withRing cRing epRingUniv nVars gRevLex
    UnivL epRing (RingTgtXs cToEp varEps) epUnivF   = epru
    nT              = cRing.fromZ
    nextT b         = rPlus cRing (cRing.times (nT 1234) b) (nT 567)
    ts              = take nVars (unfoldr (\b -> Just (b, nextT b)) (nT 12345))
    epToT           = epUnivF cRing (RingTgtXs id ts)
    varSs           = map (: []) (take nVars ['a' .. 'z'])
    GBPolyOps { pShow }     = epGBPOps gRevLex True cRing varSs (const cShow)
    testEq          = diffWith pShow (rEq epRing)
    varPowGen       = liftM2 (expt1 (epRing.times)) (Gen.element varEps)
                        (Gen.int (Range.exponential 1 200_000))
    monomGen        = do
        c       <- cGen
        varPows <- Gen.list (Range.linear 0 nVars) varPowGen
        pure $ epRing.times (cToEp c) (rProductL' epRing varPows)
    epGen           = fmap (rSumL' epRing) (Gen.list (Range.linear 0 10) monomGen)
    sg              = (pShow, epGen)
    
    props           = withRing epRing ringProps sg testEq (eiBit IsCommutativeRing)
                        ++ ringHomomProps cSG cRing testEq epRing cToEp
                        ++ [("xs", propertyOnce $ zipWithM_ (===) (map pShow varEps) varSs)]
                        ++ ringHomomProps sg epRing cTestEq cRing epToT
                        ++ [("C -> T", property $ sameFun1PT cSG cTestEq (epToT . cToEp) id),
                            ("xs ->",
                                propertyOnce $ listTestEq cShow cTestEq (map epToT varEps) ts),
                            readsProp sg testEq (polynomReads epRing (zip varSs varEps))]

testEPoly               :: IO Bool
testEPoly               = checkAll $ map test1 [1, 2, 3, 5, 9, 14, 20]
