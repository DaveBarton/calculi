{-# LANGUAGE Strict #-}

{- |  The field of integers mod @p@, for a prime @p@ that fits in a 'Word'.  -}

module Math.Algebra.Commutative.Field.ZModPW (
    Proxy(Proxy), SomeNat(SomeNat), someNatVal, Mod,
    zzModPW
) where

import Math.Algebra.General.Algebra

import Data.Mod.Word (Mod, unMod)
import Data.Proxy (Proxy(Proxy))
import GHC.TypeNats (KnownNat, SomeNat(SomeNat), natVal, someNatVal)


zzModPW         :: forall p. KnownNat p => (Field (Mod p), Mod p -> Integer)
-- ^ @p@ must be a prime, and fit in a 'Word'.
zzModPW         = (field numAG (*) 1 fromInteger recip, balRep)
  where
    p           = fromIntegral (natVal (Proxy :: Proxy p))
    maxBalRep   = p `quot` 2
    balRep x    =
        let u       = unMod x
        in  toInteger (fromIntegral (if u > maxBalRep then u - p else u) :: Int)
