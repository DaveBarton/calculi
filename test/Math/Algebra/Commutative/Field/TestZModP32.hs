{- |  This module tests the "ZModP32" module.  -}

module Math.Algebra.Commutative.Field.TestZModP32 (
    zpwTestOps, testZModP32
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.Field.ZModP32

import Math.Algebra.General.TestAlgebra

import Hedgehog ((===), annotateShow, assert)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Mod.Word (Mod)
import GHC.TypeNats (KnownNat, natVal)


zpwTestOps              :: forall p. KnownNat p => TestOps (Mod p)
-- ^ caller shows @p@
zpwTestOps              = TestOps tShow gen (===)
  where
    (zpField, balRep)   = zzModPW @p
    tShow           = show . balRep
    gen             = fmap zpField.fromZ (Gen.integral (Range.constantFrom 0 (- lim) lim))
    p               = fromIntegral (natVal (Proxy :: Proxy p))
    lim             = p `quot` 2

test1                   :: Integer -> IO Bool
test1 p                 = case someNatVal (fromInteger p) of
 SomeNat (Proxy :: Proxy p)     -> checkGroup ("ZModP32 " ++ show p) props
  where
    (zpField, balRep)   = zzModPW @p
    zpT             = zpwTestOps @p
    fromZ           = zpField.fromZ
    lim             = p `quot` 2
    props           = fieldProps zpT zpField
                        ++ [("p0", p0),
                            ("balRepIsRep", balRepIsRep), ("balRepIsSmall", balRepIsSmall)]
        -- fieldProps checks zzRing -> zpField is a homomorphism, 0 /= 1
    p0              = propertyOnce $ fromZ p === zpField.zero
    balRepIsRep     = property $ sameFun1TR zpT zpT.tEq (fromZ . balRep) id
    balRepIsSmall   = property $ do
        x       <- genVis zpT
        let n   = balRep x
        annotateShow n
        assert $ abs n <= lim
        -- if p == 2, could also specify & check (balRep zpField.one), i.e. 1 or -1

testZModP32             :: IO Bool
testZModP32             = checkAll $ map test1 primes
  where
    e2 n            = 2 ^ (n :: Int)
    primes          =
        [2, 3, 17, e2 8 - 5, e2 16 - 15, 2_000_003, e2 24 - 3, e2 31 - 1, e2 32 - 5]
        -- see https://primes.utm.edu/lists/2small/0bit.html for primes 2^n-k for small k
