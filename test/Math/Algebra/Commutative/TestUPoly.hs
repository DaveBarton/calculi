{- |  This module tests the "Math.Algebra.Commutative.UPoly" module.  -}

module Math.Algebra.Commutative.TestUPoly (
    integralPowT, upTestOps, uPolyTests
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

uPolyTests              :: TestTree
uPolyTests              = testGroup "UPoly" testsL
  where
    -- should change to a noncommutative coef ring C with zero divisors, and check X commutes
    -- with it in C[X]:
    UnivL zxRing (RingTgtX zToZX xZX) zxUnivF   = upUniv zzRing
    zxToT           = zxUnivF zzRing (RingTgtX id 12345)
    pT              =   -- polys of degree up to 10
        upTestOps zzRing (Range.linear 0 10) (zzTestOps { gen = zzExpGen 1_000_000 })
            (integralPowT "X" (Range.linear 0 10))
    monom c d       = ssLead zzRing.isZero c d ssZero
    reqFlags        =
        RingFlags { commutative = True, noZeroDivisors = True, nzInverses = False }
    
    testsL          = [ringTests pT (IsNontrivial True) reqFlags zxRing,
                        ringHomomTests (Just "Ring Homomorphism from C") zzTestOps zzRing pT.tEq
                            zxRing zToZX,
                        testOnce "x" $ pT.tEq xZX (monom 1 1),
                        ringHomomTests (Just "Ring Homomorphism to C") pT zxRing (===) zzRing
                            zxToT,
                        singleTest "C -> T" $ sameFun1TR zzTestOps (===) (zxToT . zToZX) id,
                        testOnce "x ->" $ zxToT xZX === 12345,
                        readsTest pT (polynomReads zxRing [("X", xZX)])]
