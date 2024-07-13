{-# LANGUAGE DataKinds, Strict #-}

{- |  The field of integers mod @p@, for a prime @p@ that fits in a 'Word'.  -}

module Math.Algebra.Commutative.Field.ZModPW (
    Proxy(Proxy), SomeNat(SomeNat), someNatVal, Mod,
    zzModPW, ModWord32, ModWord16, ModWord8
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


toWord          :: Mod m -> Word
-- ^ The result is @\< @m@. @@ move to Data.Mod.Word
toWord          = unsafeCoerce

unsafeFromWord  :: Word -> Mod m
-- ^ The argument must be @\< m@. @@ move to Data.Mod.Word
unsafeFromWord  = unsafeCoerce


-- | Like @Mod m@, but requiring @m \<= 2^32@; to save space e.g. in a @PrimArray@.
newtype ModWord32 (m :: Nat)    = ModW32 { w32 :: Word32 {- ^ @w32 \< m@ -} }
    deriving newtype (Eq, Show, Prim)

modWToW32       :: Mod m -> ModWord32 m
modWToW32       = ModW32 . fromIntegral . toWord

modW32ToW       :: ModWord32 m -> Mod m
modW32ToW       = unsafeFromWord . fromIntegral . (.w32)

instance KnownNat m => Num (ModWord32 m) where
    x + y           = modWToW32 $ modW32ToW x + modW32ToW y
    {-# INLINE (+) #-}
    x - y           = modWToW32 $ modW32ToW x - modW32ToW y
    {-# INLINE (-) #-}
    x * y           = modWToW32 $ modW32ToW x * modW32ToW y
    {-# INLINE (*) #-}
    negate          = modWToW32 . negate . modW32ToW
    {-# INLINE negate #-}
    abs             = id
    {-# INLINE abs #-}
    signum          = modWToW32 . signum . modW32ToW
    {-# INLINE signum #-}
    fromInteger     = modWToW32 . fromInteger
    {-# INLINE fromInteger #-}


-- | Like @Mod m@, but requiring @m \<= 2^16@; to save space e.g. in a @PrimArray@.
newtype ModWord16 (m :: Nat)    = ModW16 { w16 :: Word16 {- ^ @w16 \< m@ -} }
    deriving newtype (Eq, Show, Prim)

modWToW16       :: Mod m -> ModWord16 m
modWToW16       = ModW16 . fromIntegral . toWord

modW16ToW       :: ModWord16 m -> Mod m
modW16ToW       = unsafeFromWord . fromIntegral . (.w16)

instance KnownNat m => Num (ModWord16 m) where
    x + y           = modWToW16 $ modW16ToW x + modW16ToW y
    {-# INLINE (+) #-}
    x - y           = modWToW16 $ modW16ToW x - modW16ToW y
    {-# INLINE (-) #-}
    x * y           = modWToW16 $ modW16ToW x * modW16ToW y
    {-# INLINE (*) #-}
    negate          = modWToW16 . negate . modW16ToW
    {-# INLINE negate #-}
    abs             = id
    {-# INLINE abs #-}
    signum          = modWToW16 . signum . modW16ToW
    {-# INLINE signum #-}
    fromInteger     = modWToW16 . fromInteger
    {-# INLINE fromInteger #-}


-- | Like @Mod m@, but requiring @m \<= 2^8@; to save space e.g. in a @PrimArray@.
newtype ModWord8 (m :: Nat)    = ModW8 { w8 :: Word8 {- ^ @w8 \< m@ -} }
    deriving newtype (Eq, Show, Prim)

modWToW8        :: Mod m -> ModWord8 m
modWToW8        = ModW8 . fromIntegral . toWord

modW8ToW        :: ModWord8 m -> Mod m
modW8ToW        = unsafeFromWord . fromIntegral . (.w8)

instance KnownNat m => Num (ModWord8 m) where
    x + y           = modWToW8 $ modW8ToW x + modW8ToW y
    {-# INLINE (+) #-}
    x - y           = modWToW8 $ modW8ToW x - modW8ToW y
    {-# INLINE (-) #-}
    x * y           = modWToW8 $ modW8ToW x * modW8ToW y
    {-# INLINE (*) #-}
    negate          = modWToW8 . negate . modW8ToW
    {-# INLINE negate #-}
    abs             = id
    {-# INLINE abs #-}
    signum          = modWToW8 . signum . modW8ToW
    {-# INLINE signum #-}
    fromInteger     = modWToW8 . fromInteger
    {-# INLINE fromInteger #-}
