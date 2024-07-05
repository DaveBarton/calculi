{-# LANGUAGE DataKinds, Strict #-}

{- |  The field of integers mod @p@, for a prime @p@ that fits in a 'Word'.  -}

module Math.Algebra.Commutative.Field.ZModPW (
    Proxy(Proxy), SomeNat(SomeNat), someNatVal, Mod,
    zzModPW
) where

import Math.Algebra.General.Algebra

import Data.Mod.Word (Mod, unMod)
import Data.Primitive.Types (Prim)
import Data.Proxy (Proxy(Proxy))
import Data.Word (Word8, Word16, Word32)
import GHC.TypeNats (KnownNat, Nat, SomeNat(SomeNat), natVal, someNatVal)
import Unsafe.Coerce (unsafeCoerce)


zzModPW         :: forall p. KnownNat p => (Field (Mod p), Mod p -> Integer)
-- ^ @p@ must be a prime, and fit in a 'Word'.
zzModPW         = (field numAG (*) 1 fromInteger recip, balRep)
  where
    p           = fromIntegral (natVal (Proxy :: Proxy p))
    maxBalRep   = p `quot` 2
    balRep x    =
        let u       = unMod x
        in  toInteger (fromIntegral (if u > maxBalRep then u - p else u) :: Int)


-- types to save space from a (Mod m), e.g. in a PrimArray:

toWord          :: Mod m -> Word
-- @@ move to Data.Mod.Word
toWord          = unsafeCoerce

unsafeFromWord  :: Word -> Mod m
-- @@ move to Data.Mod.Word
unsafeFromWord  = unsafeCoerce

modW32          :: Word32 -> Mod m
modW32          = unsafeFromWord . fromIntegral

modW16          :: Word16 -> Mod m
modW16          = unsafeFromWord . fromIntegral

modW8           :: Word8 -> Mod m
modW8           = unsafeFromWord . fromIntegral

newtype ModWord32 (m :: Nat)    = ModW32 { unModW32 :: Word32 }
    deriving newtype (Eq, Show, Prim)

{- @@@@ need instance Num, better doc, ModWord16, ModWord8

instance KnownNat m => Num (ModWord32 m) where
    ModW32 x + ModW32 y     = ModW32 $ modW32 @m x + modW32 @m y
    {-# INLINE (+) #-}
    ModW32 x - ModW32 y     = ModW32 $ modW32 @m x - modW32 @m y
    {-# INLINE (-) #-}
    ModW32 x * ModW32 y     = ModW32 $ modW32 @m x * modW32 @m y
    {-# INLINE (*) #-}
-- @@@@:
    negate (ModW32 x) = Mod $ negateMod (natVal mx) x
    {-# INLINE negate #-}
    abs = id
    {-# INLINE abs #-}
    signum = const x
    where
      x = if natVal x > 1 then Mod 1 else Mod 0
    {-# INLINE signum #-}
    fromInteger x = mx
    where
      mx = Mod $ fromIntegerMod (natVal mx) x
    {-# INLINE fromInteger #-}
-}
