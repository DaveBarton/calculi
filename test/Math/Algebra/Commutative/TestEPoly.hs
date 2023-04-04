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
    cT              = zpwTestOps @2_000_003
    EPolyOps { epUniv }     = epOps cRing nVars gRevLex
    UnivL epRing (RingTgtXs cToEp varEps) epUnivF   = epUniv
    nT              = cRing.fromZ
    nextT b         = cRing.plus (cRing.times (nT 1234) b) (nT 567)
    ts              = take nVars (unfoldr (\b -> Just (b, nextT b)) (nT 12345))
    epToT           = epUnivF cRing (RingTgtXs id ts)
    varSs           = map (: []) (take nVars ['a' .. 'z'])
    GBPolyOps { pShow }     = epGBPOps gRevLex True cRing varSs (const cT.tShow) True
    varPowGen       = liftM2 (expt1 (epRing.times)) (Gen.element varEps)
                        (Gen.int (Range.exponential 1 200_000))
    monomGen        = do
        c       <- cT.gen
        varPows <- Gen.list (Range.linear 0 nVars) varPowGen
        pure $ epRing.times (cToEp c) (rProductL' epRing varPows)
    epGen           = fmap (rSumL' epRing) (Gen.list (Range.linear 0 10) monomGen)
    pT              = testOps pShow epGen epRing.eq
    
    props           = ringProps pT (eiBit IsCommutativeRing) epRing
                        ++ ringHomomProps cT cRing pT.tEq epRing cToEp
                        ++ [("xs", propertyOnce $ zipWithM_ (===) (map pShow varEps) varSs)]
                        ++ ringHomomProps pT epRing cT.tEq cRing epToT
                        ++ [("C -> T", property $ sameFun1TR cT cT.tEq (epToT . cToEp) id),
                            ("xs ->", propertyOnce $ listTestEq cT (map epToT varEps) ts),
                            readsProp pT (polynomReads epRing (zip varSs varEps))]

testEPoly               :: IO Bool
testEPoly               = checkAll $ map test1 [1, 2, 3, 5, 9, 14, 20]
