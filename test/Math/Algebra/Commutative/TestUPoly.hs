{- |  This module tests the "UPoly" module.  -}

module Math.Algebra.Commutative.TestUPoly (
    testUPoly
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.UPoly

import Math.Algebra.General.TestAlgebra

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Monad (liftM2)


testUPoly               :: IO Bool
testUPoly               = checkGroup "UPoly" props
  where
    -- should change to a noncommutative coef ring C with zero divisors, and check X commutes
    -- with it in C[X]:
    zxru            = withRing zzRing upRingUniv
    UnivL zxRing (RingTgtX zToZX xZX) zxUnivF   = zxru
    zxToT           = zxUnivF zzRing (RingTgtX id 12345)
    zxShow          = upShowPrec "X" (const show) 0
    testEq          = diffWith zxShow (rEq zxRing)
    monom c d       = ssLead (rIsZero zzRing) c d SSZero
    monomGen        = liftM2 monom (zzExpGen 1_000_000) (Gen.integral (Range.linear 0 10))
    monomsGen       = Gen.list (Range.linear 0 10) monomGen
    zxGen           = fmap (rSumL' zxRing) monomsGen
        -- polys of degree up to 10
    sg              = (zxShow, zxGen)
    props           = ringProps sg testEq zxRing ++ [commutativeProp sg testEq (rTimes zxRing)]
                        ++ ringHomomProps zzShowGen zzRing testEq zxRing zToZX
                        ++ [("x", propertyOnce $ testEq xZX (monom 1 1))]
                        ++ ringHomomProps sg zxRing (===) zzRing zxToT
                        ++ [("C -> T",
                                property $ sameFun1PT zzShowGen (===) (zxToT . zToZX) id),
                            ("x ->", propertyOnce $ zxToT xZX === 12345),
                            readsProp sg testEq (withRing zxRing polynomReads [("X", xZX)])]
