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
    UPolyOps { upUniv }     = upOps zzRing
    UnivL zxRing (RingTgtX zToZX xZX) zxUnivF   = upUniv
    zxToT           = zxUnivF zzRing (RingTgtX id 12345)
    zxShow          = upShowPrec "X" (const show) 0
    -- zxShow p        = show (ssNumTerms p) ++ "t:" ++ upShowPrec "X" (const show) 0 p
        -- for showing terms with coef 0
    monom c d       = ssLead zzRing.isZero c d SSZero
    monomGen        = liftM2 monom (zzExpGen 1_000_000) (Gen.integral (Range.linear 0 10))
    monomsGen       = Gen.list (Range.linear 0 10) monomGen
    zxGen           = fmap (rSumL' zxRing) monomsGen
        -- polys of degree up to 10
    pT              = testOps zxShow zxGen zxRing.eq
    
    props           = ringProps pT zeroBits zxRing
                        ++ ringHomomProps zzTestOps zzRing pT.tEq zxRing zToZX
                        ++ [("x", propertyOnce $ pT.tEq xZX (monom 1 1))]
                        ++ ringHomomProps pT zxRing (===) zzRing zxToT
                        ++ [("C -> T",
                                property $ sameFun1TR zzTestOps (===) (zxToT . zToZX) id),
                            ("x ->", propertyOnce $ zxToT xZX === 12345),
                            readsProp pT (polynomReads zxRing [("X", xZX)])]
