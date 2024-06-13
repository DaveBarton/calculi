{- |  This module tests the "Math.Algebra.Commutative.Field.ZModPW" module.  -}

module Math.Algebra.Commutative.Field.TestZModPW (
    zpwTestOps, zModPWTests
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.Field.ZModPW

import Math.Algebra.General.TestAlgebra

import Hedgehog ((===), diff)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Mod.Word (unMod)
import GHC.TypeNats (KnownNat, natVal)


zpwTestOps              :: forall p. KnownNat p => TestOps (Mod p)
-- ^ caller shows @p@
zpwTestOps              = TestOps tSP tCheck gen (==)
  where
    (zpField, balRep)   = zzModPW @p
    tSP             = integralPT . balRep
    tCheck notes x  = tCheckBool (showT x : notes) (unMod x < pW)
    gen             = zpField.fromZ <$> Gen.integral (Range.constantFrom 0 (- lim) lim)
    p               = fromIntegral (natVal (Proxy :: Proxy p))
    pW              = fromIntegral p :: Word
    lim             = p `quot` 2


test1                   :: SomeNat -> TestTree
test1 (SomeNat pProxy@(Proxy :: Proxy p))   = testGroup ("ZModPW " <> show p) testsL
  where
    p               = fromIntegral $ natVal pProxy  :: Integer
    (zpField, balRep)   = zzModPW @p
    zpTA            = zpwTestOps @p
    fromZ           = zpField.fromZ
    lim             = p `quot` 2
    testsL          = [fieldTests zpTA zpField, p0Test, balRepIsRep, balRepIsSmall]
        -- fieldTests checks zzRing -> zpField is a homomorphism, 0 /= 1
    p0Test          = testOnce "p0" $ fromZ p === zpField.zero
    balRepIsRep     = singleTest "balRepIsRep" $ sameFun1TR zpTA zpTA.tEq (fromZ . balRep) id
    balRepIsSmall   = singleTest "balRepIsSmall" $ do
        x       <- genVis zpTA
        let n   = balRep x
        diff (abs n) (<=) lim
        -- if p == 2, could also specify & check (balRep zpField.one), i.e. 1 or -1

zModPWTests             :: TestTree
zModPWTests             = testGroup "ZModPW" $ test1 . someNatVal <$> primes
  where
    e2 n            = 2 ^ (n :: Int)
    primes          =
        [2, 3, 17, e2 8 - 5, e2 16 - 15, 2_000_003, e2 24 - 3, e2 31 - 1, e2 32 - 5]
        -- see https://primes.utm.edu/lists/2small/0bit.html for primes 2^n-k for small k
