{-# LANGUAGE Strict #-}

{- |  The field of integers mod @p@, for a prime @p < 2^32@.  -}

module Math.Algebra.Commutative.Field.ZModP32 (
    ZModP32, zzModP32
) where

import Math.Algebra.General.Algebra

import Data.Int (Int32)
import Data.Word (Word32, Word64)


newtype ZModP32     = ZModP32 { w32 :: Word32 }     -- representatives 0 <= w < p
                        deriving Eq

zzModP32        :: Integer -> (Field ZModP32, ZModP32 -> Integer)
zzModP32 p      =
    assert (2 <= p && p < 2 ^ (32 :: Int))   -- p must also be prime
        (divisionRing ag times (ZModP32 1) (ZModP32 . fromIntegral . (`mod` p)) inv, balRep)
  where
    -- @@@ faster if we avoid `on` here & elsewhere ??:
    ag          = Group ((==) `on` w32) plus (ZModP32 0) (\ (ZModP32 x32) -> x32 == 0) neg'
    w64 x       = fromIntegral (w32 x) :: Word64
    from64 x64  = ZModP32 (fromIntegral (x64 :: Word64))
    p32         = fromIntegral p :: Word32
    p64         = fromIntegral p :: Word64
    plus x y    = let z = w64 x + w64 y in from64 (if z >= p64 then z - p64 else z)
    times x y   = from64 (w64 x * w64 y `rem` p64)
    neg' (ZModP32 x32)  = ZModP32 (if x32 == 0 then 0 else p32 - x32)
    maxBalRep32 = p32 `quot` 2
    balRep (ZModP32 x32)    = fromIntegral 
        (fromIntegral (if x32 > maxBalRep32 then x32 - p32 else x32) :: Int32)
    inv (ZModP32 x32)   = assert (x32 /= 0) (go 0 p32 1 x32)
      where     -- see https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
        go              :: Int32 -> Word32 -> Int32 -> Word32 -> ZModP32
        go t r t' r'    =   -- tx ≡ r (mod p), t'x ≡ r' (mod p), r > r' > 0
            let (q, r'')    = r `quotRem` r'
            in  if r' < 2 then
                    assert (r' == 1 && fromIntegral (abs t') <= p32 `quot` 2) $
                        let w   = fromIntegral t'
                        in  ZModP32 (if t' < 0 then w + p32 else w)
                else go t' r' (t - fromIntegral q * t') r''

-- @@ option to memoize inverses?
