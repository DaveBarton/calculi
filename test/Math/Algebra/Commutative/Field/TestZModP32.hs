{- |  This module tests the "ZModP32" module.  -}

module Math.Algebra.Commutative.Field.TestZModP32 (
    zpTestOps, testZModP32
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.Field.ZModP32

import Math.Algebra.General.TestAlgebra

import Hedgehog (annotateShow, assert)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


zpTestOps               :: Integer -> TestOps ZModP32
-- ^ caller shows @p@
zpTestOps p             = ((zpShow, gen), testEq)
  where
    (zpField, balRep)   = zzModP32 p
    zpShow          = show . balRep
    testEq          = diffWith zpShow (rEq zpField)
    gen             = fmap (rFromZ zpField) (Gen.integral (Range.constantFrom 0 (- lim) lim))
    lim             = p `quot` 2

test1                   :: Integer -> IO Bool
test1 p                 = checkGroup ("ZModP32 " ++ show p) props
  where
    (zpField, balRep)   = zzModP32 p
    (sg, testEq)    = zpTestOps p
    fromZ'          = rFromZ zpField
    lim             = p `quot` 2
    props           = withRing zpField fieldProps sg testEq
                        ++ [("p0", p0),
                            ("balRepIsRep", balRepIsRep), ("balRepIsSmall", balRepIsSmall)]
        -- fieldProps checks zzRing -> zpField is a homomorphism, 0 /= 1
    p0              = propertyOnce $ fromZ' p `testEq` rZero zpField
    balRepIsRep     = property $ sameFun1PT sg testEq (fromZ' . balRep) id
    balRepIsSmall   = property $ do
        x       <- genVis sg
        let n   = balRep x
        annotateShow n
        assert $ abs n <= lim
        -- if p == 2, could also specify & check (balRep (rOne zpField)), i.e. 1 or -1

testZModP32             :: IO Bool
testZModP32             = checkAll $ map test1 primes
  where
    e2 n            = 2 ^ (n :: Int)
    primes          =
        [2, 3, 17, e2 8 - 5, e2 16 - 15, 2_000_003, e2 24 - 3, e2 31 - 1, e2 32 - 5]
        -- see https://primes.utm.edu/lists/2small/0bit.html for primes 2^n-k for small k
