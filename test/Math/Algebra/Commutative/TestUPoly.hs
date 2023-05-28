{- |  This module tests the "UPoly" module.  -}

module Math.Algebra.Commutative.TestUPoly (
    integralPowT, upTestOps, testUPoly
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.UPoly

import Math.Algebra.General.TestAlgebra
import Math.Algebra.General.TestSparseSum

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


-- @@ move to TestSparseSum.hs !?:
integralPowT        :: (Integral d, Show d) => String -> Range d -> TestOps d
-- ^ varS prec > '^'
integralPowT varS dRange    =
    TestOps (varPowShowPrec varS) (\_ _ -> pure ()) (Gen.integral dRange) (==)

upTestOps           :: Ring c -> Range Int -> TestOps c -> TestOps Integer -> TestOps (UPoly c)
-- ^ @upTestOps cR sumRange cT dT@
upTestOps cR        = ssTestOps cR.ag compare

testUPoly               :: IO Bool
testUPoly               = checkGroup "UPoly" props
  where
    -- should change to a noncommutative coef ring C with zero divisors, and check X commutes
    -- with it in C[X]:
    UnivL zxRing (RingTgtX zToZX xZX) zxUnivF   = upUniv zzRing
    zxToT           = zxUnivF zzRing (RingTgtX id 12345)
    pT              =   -- polys of degree up to 10
        upTestOps zzRing (Range.linear 0 10) (zzTestOps { gen = zzExpGen 1_000_000 })
            (integralPowT "X" (Range.linear 0 10))
    monom c d       = ssLead zzRing.isZero c d ssZero
    
    props           = ringProps pT zeroBits zxRing
                        ++ ringHomomProps zzTestOps zzRing pT.tEq zxRing zToZX
                        ++ [("x", propertyOnce $ pT.tEq xZX (monom 1 1))]
                        ++ ringHomomProps pT zxRing (===) zzRing zxToT
                        ++ [("C -> T",
                                property $ sameFun1TR zzTestOps (===) (zxToT . zToZX) id),
                            ("x ->", propertyOnce $ zxToT xZX === 12345),
                            readsProp pT (polynomReads zxRing [("X", xZX)])]
