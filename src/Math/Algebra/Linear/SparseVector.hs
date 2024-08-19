{-# LANGUAGE Strict #-}

{- |  A sparse 'Vector' or 'VectorA' is a finite sequence of coordinates (basis coefficients),
    implemented as a (base 64) tree where zero subtrees are stored as single bits.
    
    This data structure is also efficient for vectors that are sometimes or often dense. For
    vectors that are normally extremely sparse, @IntMap@ in the @sequence@ package is better.
    
    Approximate worst-case timings are given, using \(m\) and \(n\) for vector 'size's (number
    of nonzero coordinates), and \(d = ceiling(log_{64}(max(N, 64)))\), where \(N\) is the
    maximum index plus 1. (Note the depth \(d\) is a very small positive integer.) A \"step\" is
    a small number of instructions, possibly with a single coordinate operation.
    
    It's faster to process or especially create an entire vector with a function in this module,
    rather than repeatedly indexing or setting individual coordinates.
    
    Any @S.Maybe c@ should be @S.Nothing@ if and only if the @c@ is zero (is omitted in
    'Vector's or 'VectorA's).
    
    This module uses LANGUAGE Strict. In particular, constructor fields and function arguments
    are strict unless marked with a ~. Also, a 'Vector' or 'VectorA' is strict in both its spine
    and its elements. Finally, "Data.Strict.Maybe" and "Data.Strict.Tuple" are often used.
    
    This module is normally imported qualified.
-}

module Math.Algebra.Linear.SparseVector (
    -- * Vector
    VectorA, Vector, VectorU, check,
    -- * Create
    zero, fromPIC, fromIMaybeC, fromNzIC, fromDistinctAscNzs, fromDistinctAscNzsNoCheck,
    fromDistinctNzs, fromNzs,
    -- * Query
    isZero, index, indexMaybe, size, headPairMaybe, headPair, lastPairMaybe, lastPair,
    -- * Fold
    foldBIMap', iFoldR, iFoldL, keys, toDistinctAscNzs,
    -- * Map
    mapC, mapNzFC, mapCMaybeWithIndex,
    -- * Zip/Combine
    unionWith, plusU, unionDisj, vApply, andNot, foldLIntersect',
    -- * Split/Join
    split, join,
    -- * Addition
    mkAG, mkAGU,
    -- * Multiplication
    dotWith, timesNzdC, timesNzdCU, timesC, monicizeUnit, mkModR, mkModRU,
    -- * Permute
    Permute(to, from), pToF, pIdent, pSwap, pCycle, fToP, injToPermute, pCompose, pGroup,
    permuteV, swap, sortPermute,
    -- * I/O
    showPrec
) where

import Math.Algebra.General.Algebra

import Control.Monad.Extra (pureIf)
import Control.Monad.ST (ST, runST)
import Control.Parallel.Cooperative (fbTruncLog2, lowNzBit)
import Data.Bits ((.&.), (.|.), (.^.), (!<<.), (!>>.), complement, countTrailingZeros,
    finiteBitSize, popCount)    -- @@ is countLeadingZeros faster on ARM?
import Data.Functor.Classes (liftEq)
import Data.Maybe (fromMaybe)
import qualified Data.Primitive.Contiguous as C
import Data.Primitive.PrimArray (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Primitive.Types (Prim)
import Data.Strict.Classes (toLazy)
import qualified Data.Strict.Maybe as S
import qualified Data.Strict.Tuple as S
import Data.Strict.Tuple ((:!:), pattern (:!:))
import Data.Word (Word64)
import Fmt ((+|), (|+))
import GHC.Stack (HasCallStack)


nothingIf       :: Pred a -> a -> S.Maybe a     -- move and export?
nothingIf p a   = if p a then S.Nothing else S.Just a


b64             :: Int -> Word64    -- unsafe 'bit'; 0 <= i < 64
b64 i           = 1 !<<. i

b64Index        :: Word64 -> Word64 -> Int  -- b is a bit; position in nonzero bits
b64Index b bs   = popCount ((b - 1) .&. bs)
{-# INLINE b64Index #-}

b64IndexMaybe   :: Word64 -> Word64 -> S.Maybe Int  -- like elemIndex for bits
b64IndexMaybe b bs  = if b .&. bs /= 0 then S.Just (b64Index b bs) else S.Nothing
{-# INLINE b64IndexMaybe #-}


-- @@ use C.unsafeShrinkAndFreeze after its next release, when it shrinks in place:
unsafeShrinkAndFreeze       :: (C.Contiguous arr, C.Element arr b) =>
                                C.Mutable arr s b -> Int -> ST s (arr b)
-- unsafeShrinkAndFreeze       :: SmallMutableArray s b -> Int -> ST s (SmallArray b)
unsafeShrinkAndFreeze !arr !n = do
    m       <- C.sizeMut arr
    if m == n then C.unsafeFreeze arr else C.unsafeShrinkAndFreeze arr n
  -- shrinkSmallMutableArray arr n
  -- C.unsafeFreeze arr


-- * Vector

{- | A flexible array, compressing away elements which are 0. @(arr c)@ is a small array of
    (nonzero) @c@s. -}
data VectorA arr c  = SVE { bs :: Word64, nzs :: arr c }
                    | SVV { bs :: Word64, iW2 :: Int, nzts :: SmallArray (VectorA arr c) }
    deriving (Eq, Show)     -- ^ Eq & Show e.g. for testing & debugging
{- @iW2@ is the log base 2 of the weight (max possible size) of a child tree. @iW2@ is a
    multiple of 6, and @6 <= iW2 < finiteBitSize (0 :: Int)@ in an 'SVV'. In an 'SVE', we
    consider @iW2@ to be 0.

    @testBit v.bs i@ says whether the child tree starting at @i * 2^iW2@ is nonzero, which is
    also whether it is stored in @v.nzs@/@v.nzts@.
    
    In an SVV, @bs > 1@ (except possibly for unsimplified intermediate results). -}

type Vector c   = VectorA SmallArray c
-- ^ A sparse flexible array of boxed coordinates (elements).

type VectorU c  = VectorA PrimArray c
-- ^ A sparse flexible array of unboxed coordinates (elements).

aCheck          :: (C.Contiguous arr, C.Element arr c) => Word64 -> arr c -> [Text]
aCheck bs64 nzs     = ["Lengths don't match: "+|nBs|+" and "+|nNzs|+"" | nBs /= nNzs]
  where
    nBs     = popCount bs64
    nNzs    = C.size nzs

check           :: (C.Contiguous arr, C.Element arr c) =>
                    (Int -> c -> Bool) -> VectorA arr c -> [Text]
{- ^ (Only needed for testing.) Check the integrity (internal invariants) of a vector, given an
    @omitIC@ predicate, and return a list of errors. The internal integrity of the individual
    coordinates is not checked. -}
check omitIC v  = go (finiteBitSize (0 :: Int)) v
            `orL` ["Indices not omitted: "+|zIs|+"" | not (null zIs)]
  where
    go _     (SVE bs nzs)       = aCheck bs nzs
    go parW2 (SVV bs iW2 nzts)  =
           ["iW2 too big: "+|iW2|+" >= "+|parW2|+"" | iW2 >= parW2]
        ++ ["iW2 illegal: "+|iW2|+""                | iW2 < 6 || iW2 `rem` 6 /= 0]
        ++ aCheck bs nzts
        ++ ["bs <= 1: "+|show0x bs|+""              | bs <= 1]
        ++ foldMap (go iW2) nzts
    orL x ~y    = if null x then y else x
    ~zIs        = iFoldR (\i c t -> if omitIC i c then i : t else t) [] v

getIW2          :: VectorA arr c -> Int
getIW2 (SVE {})         = 0
getIW2 (SVV _ iW2 _)    = iW2

fromMaybeSv     :: C.Contiguous arr => S.Maybe (VectorA arr c) -> VectorA arr c
fromMaybeSv     = S.fromMaybe zero

toMaybeSv       :: VectorA arr c -> S.Maybe (VectorA arr c)
toMaybeSv       = nothingIf isZero

-- * Create

zero            :: C.Contiguous arr => VectorA arr c
-- ^ A vector that is all 0s.
zero            = SVE 0 C.empty
{-# SPECIALIZE zero :: Vector c #-}

svv             :: C.Contiguous arr => Word64 -> Int -> SmallArray (VectorA arr c) ->
                    VectorA arr c
svv bs iW2 nzts
    | bs > 1        = SVV bs iW2 nzts
    | bs == 1       = C.index nzts 0
    | otherwise     = zero
{-# SPECIALIZE svv :: Word64 -> Int -> SmallArray (Vector c) -> Vector c #-}

fromPIC         :: (C.Contiguous arr, C.Element arr c) => Pred c -> Int -> c -> VectorA arr c
-- ^ Takes a @cIsZero@ predicate, and creates a singleton or empty result. \(d\) steps.
fromPIC cIsZero i c     = if cIsZero c then zero else fromNzIC i c

fromIMaybeC     :: (C.Contiguous arr, C.Element arr c) => Int -> S.Maybe c -> VectorA arr c
-- ^ Creates a singleton or empty result. \(d\) steps.
fromIMaybeC i   = S.maybe zero (fromNzIC i)

fromNzIC        :: (C.Contiguous arr, C.Element arr c) => Int -> c -> VectorA arr c
-- ^ a singleton vector. The @c@ must be nonzero. \(d\) steps.
fromNzIC i c    = if i < 0 then error "fromNzIC: negative index" else
    svv1 (i !>>. 6) 6
        (SVE (b64 (i .&. 63)) (C.singleton c))
  where
    svv1 j w2 v         = if j == 0 then v else svv1 (j !>>. 6) (w2 + 6)
        (svv (b64 (j .&. 63)) w2 (C.singleton v))
{-# SPECIALIZE fromNzIC :: Int -> c -> Vector c #-}

fromDistinctAscNzs  :: forall arr c. (C.Contiguous arr, C.Element arr c, HasCallStack) =>
                        [Int :!: c] -> VectorA arr c
{- ^ The 'Int's must be distinct and ascending, and the @c@s must be nonzero. Usually \(n\)
    steps, though up to \((d - log_{64} n) n\) if the vector is very sparse. -}
fromDistinctAscNzs ps   =
    if isSortedBy (\p q -> S.fst p < S.fst q) ps then fromDistinctAscNzsNoCheck ps
    else error "fromDistinctAscNzs: indices not distinct and ascending"
{-# SPECIALIZE fromDistinctAscNzs :: [Int :!: c] -> Vector c #-}

fromDistinctAscNzsNoCheck   :: forall arr c. (C.Contiguous arr, C.Element arr c) =>
                        [Int :!: c] -> VectorA arr c
{- ^ Like 'fromDistinctAscNzs' but the input list is not checked. If its indices are not
    distinct and ascending, undefined behavior (due to array bounds errors) may result. -}
fromDistinctAscNzsNoCheck []                    = zero
fromDistinctAscNzsNoCheck ((i0 :!: c0) : t0)    =
    if i0 < 0 then error "fromDistinctAscNzs: negative index" else runST $ do
    sveBuf          <- C.new @arr 64
    let mkSve bs j i c ics  = do
            C.write sveBuf j c
            case ics of
                (i' :!: c') : t
                    | i' <= i .|. 63    -> mkSve bs' (j + 1) i' c' t
                _                       -> do
                    nzs'    <- C.freeze (C.sliceMut sveBuf 0 (j + 1))
                    pure (SVE bs' nzs' :!: ics)
          where
            bs'         = bs .|. b64 (i .&. 63)
        mkSvv bs iW2 nzts j i c ics     = do
            v :!: t     <- mkSV (iW2 - 6) i c ics
            C.write nzts j v
            case t of
                (i' :!: c') : t'    -- beware: iW2 + 6 may be too big for b64:
                    | i' !>>. iW2 <= iRsh .|. 63    -> mkSvv bs' iW2 nzts (j + 1) i' c' t'
                _                                   -> do
                    nzts'   <- unsafeShrinkAndFreeze nzts (j + 1)
                    pure (svv bs' iW2 nzts' :!: t)
          where
            iRsh        = i !>>. iW2
            bs'         = bs .|. b64 (iRsh .&. 63)
        mkSV iW2 i c ics    = if iW2 == 0 then mkSve 0 0 i c ics else do
            nzts        <- C.new 64
            mkSvv 0 iW2 nzts 0 i c ics
        trunc6 n    = n - n `rem` 6     -- same as n `quot` 6 * 6
    S.fst <$> mkSV (trunc6 (fbTruncLog2 (maxBound :: Int))) i0 c0 t0
{-# SPECIALIZE fromDistinctAscNzsNoCheck :: [Int :!: c] -> Vector c #-}

fromDistinctNzs     :: forall arr c. (C.Contiguous arr, C.Element arr c) =>
                        [Int :!: c] -> VectorA arr c
{- ^ The 'Int's must be distinct, and the @c@s must be nonzero. \(O(n log_2 n)\). -}
fromDistinctNzs     = fromDistinctAscNzs . sortLBy (compare `on` S.fst)
    -- @@ parallelize?
{-# SPECIALIZE fromDistinctNzs :: [Int :!: c] -> Vector c #-}

fromNzs             :: forall arr c. (C.Contiguous arr, C.Element arr c) => [c] -> VectorA arr c
{- ^ The @c@s must be nonzero. \(n\) steps. -}
fromNzs             = fromDistinctAscNzsNoCheck . S.zip [0 ..]
{-# SPECIALIZE fromNzs :: [c] -> Vector c #-}

-- * Query

isZero          :: VectorA arr c -> Bool
-- ^ 1 step.
isZero v        = v.bs == 0
{-# INLINE isZero #-}

index           :: (C.Contiguous arr, C.Element arr c) => c -> VectorA arr c -> Int -> c
-- ^ @index cZero v i = v[i]@, the @i@'th coordinate of @v@. @i >= 0@. \(d\) steps.
index cZero vRoot iRoot     = S.fromMaybe cZero (indexMaybe vRoot iRoot)
{-# INLINE index #-}

indexMaybe      :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> Int -> S.Maybe c
-- ^ Like 'index'. \(d\) steps.
indexMaybe vRoot iRoot
    | iRoot < 0     = error ("SV.indexMaybe: negative index " <> show iRoot)
    | otherwise     = go vRoot iRoot
  where
    i0ToMJ i0 bs            = if i0 > 63 then S.Nothing else b64IndexMaybe (b64 i0) bs
    go (SVE bs nzs) i       = C.index nzs <$> i0ToMJ i bs
    go (SVV bs iW2 nzts) i  = S.maybe S.Nothing jF (i0ToMJ (i !>>. iW2) bs)
      where
        jF j        = go (C.index nzts j) (i .&. ((1 !<<. iW2) - 1))
{-# SPECIALIZE indexMaybe :: Vector c -> Int -> S.Maybe c #-}

size            :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> Int
{- ^ \(n\), the number of nonzero coefficients. \(n / 64\) steps for a dense vector, to \(d n\)
    steps for a very sparse one. -}
size (SVE bs _)         = popCount bs
size (SVV _ _ nzts)     = foldl' (\acc t -> acc + size t) 0 nzts
{-# SPECIALIZE size :: Vector c -> Int #-}

headPairMaybe   :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> S.Maybe (Int :!: c)
-- ^ The nonzero term with minimal index. \(d\) steps.
headPairMaybe   = iFoldR (\i c _ -> S.Just (i :!: c)) S.Nothing
{-# SPECIALIZE headPairMaybe :: Vector c -> S.Maybe (Int :!: c) #-}

headPair        :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> Int :!: c
-- ^ @S.fromJust . headPairMaybe@. \(d\) steps.
headPair        = S.fromJust . headPairMaybe
{-# SPECIALIZE headPair :: Vector c -> Int :!: c #-}

lastPairMaybe   :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> S.Maybe (Int :!: c)
-- ^ The nonzero term with maximal index. \(d\) steps.
lastPairMaybe   = iFoldL (\i _ c -> S.Just (i :!: c)) S.Nothing
{-# SPECIALIZE lastPairMaybe :: Vector c -> S.Maybe (Int :!: c) #-}

lastPair        :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> Int :!: c
-- ^ @S.fromJust . lastPairMaybe@. \(d\) steps.
lastPair        = S.fromJust . lastPairMaybe
{-# SPECIALIZE lastPair :: Vector c -> Int :!: c #-}

-- * Fold

aFoldBIMap'     :: (C.Contiguous arr, C.Element arr c) => Op2 t -> (Int -> c -> t) -> Int ->
                    Word64 -> Int -> arr c -> t
aFoldBIMap' tOp iCToT start bs64 iW2 nzs    = go bs64 0 32 0
  where
    -- bs /= 0:
    go _  i0 0 j    = iCToT !$ start + i0 !<<. iW2 !$ C.index nzs j
    go bs i0 d j
        | highBs == 0   = go lowBs  i0 d' j
        | lowBs == 0    = go highBs i1 d' j
        | otherwise     = tOp !$ go lowBs i0 d' j !$ go highBs i1 d' (j + popCount lowBs)
      where
        i1      = i0 + d
        lowBs   = bs .&. (b64 i1 - 1)
        highBs  = bs .^. lowBs
        d'      = d !>>. 1
{-# SPECIALIZE aFoldBIMap' :: Op2 t -> (Int -> c -> t) -> Int -> Word64 -> Int -> SmallArray c
    -> t #-}

foldBIMap'      :: (C.Contiguous arr, C.Element arr c) => Op2 t -> t -> (Int -> c -> t) ->
                    VectorA arr c -> t
{- ^ Bottom-up strict fold with index, to a monoid (associative operation with identity). \(m\)
    steps. -}
foldBIMap' _   ~tIdent _     (SVE 0 _)  = tIdent
foldBIMap' tOp ~_      iCToT v          = go 0 v
  where
    go start (SVE bs nzs)       = aFoldBIMap' tOp iCToT start bs 0   nzs
    go start (SVV bs iW2 nzts)  = aFoldBIMap' tOp go    start bs iW2 nzts
{-# SPECIALIZE foldBIMap' :: Op2 t -> t -> (Int -> c -> t) -> Vector c -> t #-}

aIFoldR         :: (C.Contiguous arr, C.Element arr c) => (Int -> c -> t -> t) -> t -> Int ->
                    Word64 -> Int -> arr c -> t
aIFoldR f ~z start bs iW2 nzs   = go bs 0
  where
    go 0      _         = z
    go bsTodo j         = f i (C.index nzs j) (go bsTodo' (j + 1))
      where
        i           = start + countTrailingZeros bsTodo !<<. iW2
        bsTodo'     = bsTodo .^. lowNzBit bsTodo
{-# SPECIALIZE aIFoldR :: (Int -> c -> t -> t) -> t -> Int -> Word64 -> Int -> SmallArray c ->
    t #-}

iFoldR          :: (C.Contiguous arr, C.Element arr c) => (Int -> c -> t -> t) -> t ->
                    VectorA arr c -> t
-- ^ Lazy right fold with index. Missing elements are skipped. \(m\) steps.
iFoldR f        = flip (go 0)
  where
    go start (SVE bs nzs)      ~z   = aIFoldR f  z start bs 0   nzs
    go start (SVV bs iW2 nzts) ~z   = aIFoldR go z start bs iW2 nzts
{-# SPECIALIZE iFoldR :: (Int -> c -> t -> t) -> t -> Vector c -> t #-}

aIFoldL         :: (C.Contiguous arr, C.Element arr c) => (Int -> t -> c -> t) -> t -> Int ->
                    Word64 -> Int -> arr c -> t
aIFoldL f ~z start bs iW2 nzs   = go bs (popCount bs - 1)
  where
    go 0      _         = z
    go bsTodo j         = f i (go bsTodo' (j - 1)) (C.index nzs j)
      where
        i0          = fbTruncLog2 bsTodo
        i           = start + i0 !<<. iW2
        bsTodo'     = bsTodo .^. b64 i0
{-# SPECIALIZE aIFoldL :: (Int -> t -> c -> t) -> t -> Int -> Word64 -> Int -> SmallArray c ->
    t #-}

iFoldL          :: (C.Contiguous arr, C.Element arr c) => (Int -> t -> c -> t) -> t ->
                    VectorA arr c -> t
-- ^ Lazy left fold with index. Missing elements are skipped. \(m\) steps.
iFoldL f        = go 0
  where
    go start ~z (SVE bs nzs)        = aIFoldL f  z start bs 0   nzs
    go start ~z (SVV bs iW2 nzts)   = aIFoldL go z start bs iW2 nzts
{-# SPECIALIZE iFoldL :: (Int -> t -> c -> t) -> t -> Vector c -> t #-}

keys            :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> [Int]
-- ^ Non-missing indices of the vector, in increasing order. \(m\) steps.
keys            = iFoldR (\i _c -> (i :)) []
{-# SPECIALIZE keys :: Vector c -> [Int] #-}

toDistinctAscNzs    :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> [Int :!: c]
-- ^ @toDistinctAscNzs = iFoldR (\i c -> ((i :!: c) :)) []@. \(m\) steps.
toDistinctAscNzs    = iFoldR (\i c -> ((i :!: c) :)) []
{-# SPECIALIZE toDistinctAscNzs :: Vector c -> [Int :!: c] #-}

-- * Map

mkSv            :: C.Contiguous arr' =>
    (Word64 -> arr c -> Word64 :!: arr' c') ->
    (Word64 -> SmallArray (VectorA arr c) -> Word64 :!: SmallArray (VectorA arr' c')) ->
    VectorA arr c -> VectorA arr' c'
mkSv sveF _ (SVE bs nzs)        = S.uncurry SVE $ sveF bs nzs
mkSv _ svvF (SVV bs iW2 nzts)   = svv bs' iW2 nzts'
  where
    bs' :!: nzts'   = svvF bs nzts

combineSv       :: C.Contiguous arr2 =>
    (Word64 -> arr0 c0 -> Word64 -> arr1 c1 -> Word64 :!: arr2 c2) ->
    (Int -> Word64 -> SmallArray (VectorA arr0 c0) -> Word64 -> SmallArray (VectorA arr1 c1) ->
        Word64 :!: SmallArray (VectorA arr2 c2)) ->
    VectorA arr0 c0 -> VectorA arr1 c1 -> VectorA arr2 c2
{- For speed, the caller may want to check isZero, or getIW2 x < or > getIW2 y. Else note svvF
    may be passed an unnormalized argument. -}
combineSv sveF svvF     = go
  where
    go (SVE bs0 nzs0) (SVE bs1 nzs1)    = S.uncurry SVE $ sveF bs0 nzs0 bs1 nzs1
    go x y
        | getIW2 x > getIW2 y           = go x (SVV 1 (getIW2 x) (C.singleton y))
        | getIW2 x < getIW2 y           = go (SVV 1 (getIW2 y) (C.singleton x)) y
    go (SVV bs0 iW2 nzts0) (SVV bs1 _ nzts1)    = svv bs2 iW2 nzts2
      where
        bs2 :!: nzts2   = svvF iW2 bs0 nzts0 bs1 nzts1
    go _ _                              = undefined

aMapC           :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c') =>
                    Pred c' -> (c -> c') -> Word64 -> arr c -> Word64 :!: arr' c'
-- assumes @popCount bs == C.size nzs@
aMapC is0 f bs nzs    = assert (popCount bs == C.size nzs) $ runST $ do
    nzs'    <- C.new (C.size nzs)
    let go 0      bs' _ j'  = (bs' :!:) <$> unsafeShrinkAndFreeze nzs' j'
        go bsTodo bs' j j'  = if is0 c' then go (bsTodo .^. b) (bs' .^. b) (j + 1) j' else do
            C.write nzs' j' c'
            go (bsTodo .^. b) bs' (j + 1) (j' + 1)
          where
            b       = lowNzBit bsTodo
            c'      = f $! C.index nzs j
    go bs bs 0 0
{-# SPECIALIZE aMapC :: Pred c' -> (c -> c') -> Word64 -> SmallArray c ->
    Word64 :!: SmallArray c' #-}

mapC            :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c') =>
                    Pred c' -> (c -> c') -> VectorA arr c -> VectorA arr' c'
{- ^ @mapC isZero'@ assumes the @(c -> c')@ takes zero to zero. Usually \(m\) steps, or up to
    \((d - log_{64} m) m\) for a very sparse vector. -}
mapC is0 f  = go
  where
    go      = mkSv (aMapC is0 f) (aMapC isZero go)
{-# SPECIALIZE mapC :: Pred c' -> (c -> c') -> Vector c -> Vector c' #-}

mapNzFC         :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c') =>
                    (c -> c') -> VectorA arr c -> VectorA arr' c'
{- ^ assumes the @(c -> c')@ takes zero to zero, and nonzero values to nonzero values. Usually
    \(m\) steps, or up to \((d - log_{64} m) m\) for a very sparse vector. -}
mapNzFC f (SVE bs nzs)          = SVE bs (C.map' f nzs)
mapNzFC f (SVV bs iW2 nzts)     = SVV bs iW2 (C.map' (mapNzFC f) nzts)
{-# SPECIALIZE mapNzFC :: (c -> c') -> Vector c -> Vector c' #-}

aMapCMaybeWithIndex     :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr',
                            C.Element arr' c') => (Int -> c -> S.Maybe c') -> Int ->
                            Word64 -> Int -> arr c -> Word64 :!: arr' c'
aMapCMaybeWithIndex f start bs iW2 nzs  = assert (popCount bs == C.size nzs) $ runST $ do
    nzs'    <- C.new (C.size nzs)
    let go 0      bs' _ j'  = (bs' :!:) <$> unsafeShrinkAndFreeze nzs' j'
        go bsTodo bs' j j'  = case mc' of
            S.Nothing   -> go (bsTodo .^. b) (bs' .^. b) (j + 1) j'
            S.Just c'   -> do
                C.write nzs' j' c'
                go (bsTodo .^. b) bs' (j + 1) (j' + 1)
          where
            i0      = countTrailingZeros bsTodo
            mc'     = f !$ start + i0 !<<. iW2 !$ C.index nzs j
            b       = b64 i0
    go bs bs 0 0
{-# INLINABLE aMapCMaybeWithIndex #-}
{-# SPECIALIZE aMapCMaybeWithIndex :: (Int -> c -> S.Maybe c') -> Int ->
                    Word64 -> Int -> SmallArray c -> Word64 :!: SmallArray c' #-}

mapCMaybeWithIndex  :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c')
                        => (Int -> c -> S.Maybe c') -> VectorA arr c -> VectorA arr' c'
{- ^ @mapCMaybeWithIndex f@ assumes @f i zero@ is zero, for all @i@. Usually \(m\) steps, or up
    to \((d - log_{64} m) m\) for a very sparse vector. -}
mapCMaybeWithIndex f    = fromMaybeSv . go 0
  where
    go start (SVE bs nzs)       = toMaybeSv $ SVE bs' nzs'
      where
        bs' :!: nzs'    = aMapCMaybeWithIndex f start bs 0 nzs
    go start (SVV bs iW2 nzts)  = toMaybeSv $ svv bs' iW2 nzts'
      where
        bs' :!: nzts'   = aMapCMaybeWithIndex go start bs iW2 nzts
{-# INLINABLE mapCMaybeWithIndex #-}
{-# SPECIALIZE mapCMaybeWithIndex :: (Int -> c -> S.Maybe c') -> Vector c -> Vector c' #-}

-- * Zip/Combine

aUnionWith      :: (C.Contiguous arr, C.Element arr c) => Pred c -> Op2 c ->
                    Word64 -> arr c -> Word64 -> arr c -> Word64 :!: arr c
-- assumes @f c zero == f zero c == c@ and
-- @popCount bs0 == C.size nzs0 && popCount bs1 == C.size nzs1@
aUnionWith _   _ bs0 nzs0 bs1 nzs1  -- to make SV.join fast
    | bs0 < lowNzBit bs1            = bs0 .|. bs1 :!: C.append nzs0 nzs1
aUnionWith is0 f bs0 nzs0 bs1 nzs1  = runST $ do
    let bsAll   = bs0 .|. bs1
    nzs2        <- C.new (popCount bsAll)
    let go 0      bs2 _  _  j2  = (bs2 :!:) <$> unsafeShrinkAndFreeze nzs2 j2
        go bsTodo bs2 j0 j1 j2
            | bs0 .&. b == 0        = do
                C.write nzs2 j2 $! C.index nzs1 j1
                go bsTodo' bs2 j0 (j1 + 1) (j2 + 1)
            | bs1 .&. b == 0        = do
                C.write nzs2 j2 $! C.index nzs0 j0
                go bsTodo' bs2 (j0 + 1) j1 (j2 + 1)
            | otherwise             = do
                let c       = f !$ C.index nzs0 j0 !$ C.index nzs1 j1
                if is0 c then go bsTodo' (bs2 .^. b) (j0 + 1) (j1 + 1) j2 else do
                    C.write nzs2 j2 c
                    go bsTodo' bs2 (j0 + 1) (j1 + 1) (j2 + 1)
          where
            b           = lowNzBit bsTodo
            bsTodo'     = bsTodo .^. b
    go bsAll bsAll 0 0 0
{-# SPECIALIZE aUnionWith :: Pred c -> Op2 c ->
    Word64 -> SmallArray c -> Word64 -> SmallArray c -> Word64 :!: SmallArray c #-}

unionWith       :: (C.Contiguous arr, C.Element arr c) => Pred c -> Op2 c -> Op2 (VectorA arr c)
{- ^ @unionWith is0 f@ assumes @f c zero == f zero c == c@. \(m + n\) steps, or more precisely
    for sparse vectors, \(k + b t\) where \(k\) and \(t\) are the inputs' number of common
    indices and tree nodes respectively, and \(b\) is a small constant. -}
unionWith is0 f     = go
  where
    go (SVE bs0 nzs0) (SVE bs1 nzs1)    = S.uncurry SVE $ aUnionWith is0 f bs0 nzs0 bs1 nzs1
    go x y
        | getIW2 x > getIW2 y           = goGT x y False
        | getIW2 x < getIW2 y           = goGT y x True
    go (SVV bs0 iW2 nzts0) (SVV bs1 _ nzts1)    = svv bs2 iW2 nzts2
      where
        bs2 :!: nzts2   = aUnionWith isZero go bs0 nzts0 bs1 nzts1
    go _ _                              = undefined
    goGT x@(SVV bs iW2 nzts) v doFlip
        | isZero v          = x
        | bs .&. 1 == 0     = SVV (bs .|. 1) iW2 (C.insertAt nzts 0 v)
        | isZero v0         = SVV (bs .^. 1) iW2 (C.deleteAt nzts 0)
        | otherwise         = SVV bs         iW2 (C.replaceAt nzts 0 $! v0)
      where
        ~v0             = if doFlip then go v (C.index nzts 0) else go (C.index nzts 0) v
    goGT (SVE {}) _ _           = undefined
{-# SPECIALIZE unionWith :: Pred c -> Op2 c -> Op2 (Vector c) #-}

aPlusU          :: (Eq c, Num c, Prim c) => Word64 -> PrimArray c -> Word64 -> PrimArray c ->
                    Word64 :!: PrimArray c
-- assumes @popCount bs0 == C.size nzs0 && popCount bs1 == C.size nzs1@
aPlusU bs0 nzs0 bs1 nzs1    = runST $ do
    let bsAll   = bs0 .|. bs1
    nzs2        <- C.new (popCount bsAll)
    let go 0      bs2 _  _  j2  = (bs2 :!:) <$> unsafeShrinkAndFreeze nzs2 j2
        go bsTodo bs2 j0 j1 j2
            | bs0 .&. b == 0        = do
                C.write nzs2 j2 $! C.index nzs1 j1
                go bsTodo' bs2 j0 (j1 + 1) (j2 + 1)
            | bs1 .&. b == 0        = do
                C.write nzs2 j2 $! C.index nzs0 j0
                go bsTodo' bs2 (j0 + 1) j1 (j2 + 1)
            | otherwise             = do
                let c       = C.index nzs0 j0 + C.index nzs1 j1
                if c == 0 then go bsTodo' (bs2 .^. b) (j0 + 1) (j1 + 1) j2 else do
                    C.write nzs2 j2 c
                    go bsTodo' bs2 (j0 + 1) (j1 + 1) (j2 + 1)
          where
            b           = lowNzBit bsTodo
            bsTodo'     = bsTodo .^. b
    go bsAll bsAll 0 0 0
{-# INLINABLE aPlusU #-}

plusU           :: (Eq c, Num c, Prim c) => Op2 (VectorU c)
{- ^ \(m + n\) steps, or more precisely for sparse vectors, \(k + b t\) where \(k\) and \(t\)
    are the inputs' number of common indices and tree nodes respectively, and \(b\) is a
    small constant. -}
plusU           = go
  where
    go (SVE bs0 nzs0) (SVE bs1 nzs1)    = S.uncurry SVE $ aPlusU bs0 nzs0 bs1 nzs1
    go x y
        | getIW2 x > getIW2 y           = goGT x y
        | getIW2 x < getIW2 y           = goGT y x
    go (SVV bs0 iW2 nzts0) (SVV bs1 _ nzts1)    = svv bs2 iW2 nzts2
      where
        bs2 :!: nzts2   = aUnionWith isZero go bs0 nzts0 bs1 nzts1
    go _ _                              = undefined
    goGT x@(SVV bs iW2 nzts) v
        | isZero v          = x
        | bs .&. 1 == 0     = SVV (bs .|. 1) iW2 (C.insertAt nzts 0 v)
        | isZero v0         = SVV (bs .^. 1) iW2 (C.deleteAt nzts 0)
        | otherwise         = SVV bs         iW2 (C.replaceAt nzts 0 $! v0)
      where
        ~v0             = go (C.index nzts 0) v
    goGT (SVE {}) _             = undefined
{-# INLINABLE plusU #-}

unionDisj       :: (C.Contiguous arr, C.Element arr c, HasCallStack) => Op2 (VectorA arr c)
{- ^ The union of two disjoint vectors. They must have no common indices. \(O(m + n)\), or less
    if the vectors have large non-overlapping subtrees. -}
unionDisj       = unionWith (const False) (\_ _ -> error "unionDisj: Non-disjoint vectors")
{-# SPECIALIZE unionDisj :: Op2 (Vector c) #-}
{-# INLINEABLE unionDisj #-}

aVApply         :: (C.Contiguous dArr, C.Element dArr d, C.Contiguous cArr, C.Element cArr c) =>
                    (Int -> d -> Op1 (S.Maybe c)) -> Int -> Int ->
                    Word64 -> dArr d -> Word64 -> cArr c -> Word64 :!: cArr c
aVApply f start iW2 bs0 nzs0 bs1 nzs1   = runST $ do
    let bsAll   = bs0 .|. bs1
    nzs2        <- C.new (popCount bsAll)
    let go 0      bs2 _  _  j2  = (bs2 :!:) <$> unsafeShrinkAndFreeze nzs2 j2
        go bsTodo bs2 j0 j1 j2
            | bs0 .&. b == 0        = do
                C.write nzs2 j2 $! C.index nzs1 j1
                go bsTodo' bs2 j0 (j1 + 1) (j2 + 1)
            | bs1 .&. b == 0        = goD S.Nothing j1
            | otherwise             = goD (S.Just (C.index nzs1 j1)) (j1 + 1)
          where
            b               = lowNzBit bsTodo
            bsTodo'         = bsTodo .^. b
            goD mc1 j1'     =
                case f !$ start + i0 !<<. iW2 !$ C.index nzs0 j0 !$ mc1 of
                    S.Nothing       -> go bsTodo' (bs2 .^. b) (j0 + 1) j1' j2
                    S.Just c        -> do
                        C.write nzs2 j2 c
                        go bsTodo' bs2 (j0 + 1) j1' (j2 + 1)
              where
                i0              = fbTruncLog2 b
    go bsAll bsAll 0 0 0
{-# SPECIALIZE aVApply :: (Int -> d -> Op1 (S.Maybe c)) -> Int -> Int
    -> Word64 -> SmallArray d -> Word64 -> SmallArray c -> Word64 :!: SmallArray c #-}

vApply          :: (C.Contiguous dArr, C.Element dArr d, C.Contiguous cArr, C.Element cArr c) =>
                    (Int -> d -> Op1 (S.Maybe c)) -> VectorA dArr d -> Op1 (VectorA cArr c)
{- ^ @vApply f ds v@ applies @f i ds[i]@ to @v[i]@, for each non-missing element in @ds@.
    Usually \(m + n\) steps, though \(m\) if the input trees have few common nodes, or up to
    \(64 (d - log_{64} m) m\) if the first input is very sparse and the second input is very
    dense. -}
vApply f ds0 v0     = fromMaybeSv $ go 0 ds0 (toMaybeSv v0)
  where
    go start ds mv
        | S.Nothing <- mv   = toMaybeSv $
                                mapCMaybeWithIndex (\i d -> f (start + i) d S.Nothing) ds
        | isZero ds         = mv
        | S.Just v  <- mv   = toMaybeSv $ combineSv (aVApply f start 0) (aVApply go start) ds v
{-# SPECIALIZE vApply :: (Int -> d -> Op1 (S.Maybe c)) -> Vector d -> Op1 (Vector c) #-}
-- @@ elim. vApply, and Maybe functions in this file ?

sveSelect       :: (C.Contiguous arr, C.Element arr c) => Word64 -> Op1 (VectorA arr c)
sveSelect bs1 v0@(SVE bs0 arr0)
    | bs == bs0     = v0
    | bs == 0       = zero
    | otherwise     = runST $ do
        a       <- C.new (popCount bs)
        let go 0      _     = SVE bs <$> C.unsafeFreeze a
            go bsTodo j     = do
                C.write a j $! C.index arr0 (b64Index b bs0)
                go bsTodo' (j + 1)
              where
                b           = lowNzBit bsTodo
                bsTodo'     = bsTodo .^. b
        go bs 0
  where
    bs      = bs0 .&. bs1
sveSelect _ _   = undefined
{-# INLINE sveSelect #-}

andNot          :: (C.Contiguous arr0, C.Element arr0 c0, C.Contiguous arr1, C.Element arr1 c1)
                    => VectorA arr0 c0 -> VectorA arr1 c1 -> VectorA arr0 c0
{- Like a set difference, restrict the first vector to its keys that don't occur in the second
    one. \(O(m)\), but usually just 1 step for each subtree in the first vector that isn't in
    the second one. -}
andNot v@(SVE {}) (SVE bs1 _)   = sveSelect (complement bs1) v
andNot x          y
    | getIW2 x < getIW2 y   = if y.bs .&. 1 /= 0 then andNot x (C.index y.nzts 0) else x
    | getIW2 x > getIW2 y   = if x.bs .&. 1 == 0 || isZero y then x
                              else andNot x (SVV 1 x.iW2 (C.singleton y))
    | x.bs .&. y.bs == 0    = x
andNot (SVV bs0 iW2 nzts0) (SVV bs1 _ nzts1)    = runST $ do    -- same iW2
    nzts2       <- C.new (popCount bs0)
    let go 0      bs2 _  j2     = svv bs2 iW2 <$> unsafeShrinkAndFreeze nzts2 j2
        go bsTodo bs2 j0 j2
            | bs1 .&. b == 0        = do
                C.write nzts2 j2 $! C.index nzts0 j0
                go bsTodo' bs2 (j0 + 1) (j2 + 1)
            | otherwise             = do
                let t       = andNot !$ C.index nzts0 j0 !$ C.index nzts1 (b64Index b bs1)
                if isZero t then go bsTodo' (bs2 .^. b) (j0 + 1) j2 else do
                    C.write nzts2 j2 t
                    go bsTodo' bs2 (j0 + 1) (j2 + 1)
          where
            b           = lowNzBit bsTodo
            bsTodo'     = bsTodo .^. b
    go bs0 bs0 0 0
andNot _ _                      = undefined
{-# SPECIALIZE andNot :: Vector c0 -> Vector c1 -> Vector c0 #-}

aFoldLIntersect'    :: (C.Contiguous arr0, C.Element arr0 c0,
                        C.Contiguous arr1, C.Element arr1 c1) =>
                        (t -> c0 -> c1 -> t) -> t -> Word64 -> arr0 c0 -> Word64 -> arr1 c1 -> t
aFoldLIntersect' f t bs0 nzs0 bs1 nzs1  = go t (bs0 .&. bs1)
  where
    go acc 0        = acc
    go acc bsTodo   = go acc' bsTodo'
      where
        b               = lowNzBit bsTodo
        jF              = b64Index b
        acc'            = f acc !$ C.index nzs0 (jF bs0) !$ C.index nzs1 (jF bs1)
        bsTodo'         = bsTodo .^. b
{-# SPECIALIZE aFoldLIntersect' :: (t -> c0 -> c1 -> t) -> t -> Word64 -> SmallArray c0 ->
    Word64 -> SmallArray c1 -> t #-}

foldLIntersect'     :: (C.Contiguous arr0, C.Element arr0 c0,
                        C.Contiguous arr1, C.Element arr1 c1) =>
                        (t -> c0 -> c1 -> t) -> t -> VectorA arr0 c0 -> VectorA arr1 c1 -> t
{- ^ Strict left fold over the intersection (common indices) of two vectors. \(O(m + n)\), but
    usually just 1 step for each common node or index. -}
foldLIntersect' f   = go
  where
    go t (SVE bs0 nzs0)     (SVE bs1 nzs1)      = aFoldLIntersect' f t bs0 nzs0 bs1 nzs1
    go t x                  y
        | getIW2 x > getIW2 y   = if x.bs .&. 1 /= 0 then go t (C.index x.nzts 0) y else t
        | getIW2 x < getIW2 y   = if y.bs .&. 1 /= 0 then go t x (C.index y.nzts 0) else t
    go t (SVV bs0 _ nzts0) (SVV bs1 _ nzts1)    = aFoldLIntersect' go t bs0 nzts0 bs1 nzts1
    go _ _                 _                    = undefined
{-# SPECIALIZE foldLIntersect' :: (t -> c0 -> c1 -> t) -> t -> Vector c0 -> Vector c1 -> t #-}

-- * Split/Join

split           :: (C.Contiguous arr, C.Element arr c) => Int -> VectorA arr c ->
                    VectorA arr c :!: VectorA arr c
{- ^ @split i v@ splits @v@ into parts with indices @\< i@, and @>= i@. Up to \(64 d\) steps
    for a dense @v@, or fewer if @i@ is a multiple of a high power of 2. -}
split i         = go (max i 0)
  where
    go k w
        | w.bs == lowBs         = w :!: zero
        | k == 0                = zero :!: w
        | SVE bs nzs    <- w    = SVE lowBs          (C.clone (C.slice nzs 0 j))
                              :!: SVE (bs .^. lowBs) (C.clone (C.slice nzs j (n1s - j)))
        | SVV bs iW2 nzts   <- w,
          let highBs        = bs .&. (negate 2 !<<. k0)
              v0            = svv lowBs  iW2 (C.clone (C.slice nzts 0 j))
              j1            = if bs .&. b == 0 then j else j + 1
              v3            = svv highBs iW2 (C.clone (C.slice nzts j1 (n1s - j1)))
            = if bs .&. b == 0 then v0 :!: v3 else
                let v1 :!: v2   = go (k - k0 !<<. iW2) (C.index nzts j)
                    raise v     = if isZero v then v else svv b iW2 (C.singleton v)
                in  join v0 (raise v1) :!: join (raise v2) v3
      where
        k0          = k !>>. getIW2 w
        b           = if k0 >= 64 then 0 else b64 k0
        lowBs       = w.bs .&. (b - 1)
        ~j          = popCount lowBs
        ~n1s        = popCount w.bs
{-# SPECIALIZE split :: Int -> Vector c -> Vector c :!: Vector c #-}

join            :: (C.Contiguous arr, C.Element arr c, HasCallStack) => Op2 (VectorA arr c)
{- ^ Concatenate two vectors, e.g. undoing a 'split'. The indices in the first must be smaller
    than the indices in the second. Up to \(64 d\) steps for a dense vector, or fewer if the
    parts were split at a multiple of a high power of 2. -}
join            = unionDisj
{-# INLINE join #-}

-- * Addition

mkAG            :: (C.Contiguous arr, C.Element arr c) =>
                    AbelianGroup c -> AbelianGroup (VectorA arr c)
-- ^ Addition of vectors takes the same time as 'unionWith'.
mkAG ag         = AbelianGroup svFlags svEq svPlus zero isZero (mapNzFC ag.neg)
  where
    svEq (SVE bs nzs)      (SVE bs' nzs')           =
        bs == bs' && C.foldrZipWith (\c c' ~b -> ag.eq c c' && b) True nzs nzs'
    svEq (SVV bs iW2 nzts) (SVV bs' iW2' nzts')     =
        bs == bs' && iW2 == iW2' && liftEq svEq nzts nzts'
    svEq _                 _                        = False
    
    svPlus          = unionWith ag.isZero ag.plus
    svFlags         = agFlags (IsNontrivial ag.monFlags.nontrivial)
{-# SPECIALIZE mkAG :: AbelianGroup c -> AbelianGroup (Vector c) #-}

mkAGU           :: (Eq c, Num c, Prim c) => AbelianGroup (VectorU c)
-- ^ 'mkAG' with unboxed coordinates.
mkAGU           = (mkAG numAG) { plus = plusU }
{-# INLINABLE mkAGU #-}

-- * Multiplication

aDotWith        :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr1, C.Element arr1 c1) =>
                    AbelianGroup c2 -> (c -> c1 -> c2) -> Word64 -> arr c ->
                    Word64 -> arr1 c1 -> c2
-- @aDotWith tAG f@ assumes @f c zero == f zero c1 == zero@ and
-- @popCount bs0 == C.size nzs0 && popCount bs1 == C.size nzs1@
aDotWith tAG f bs0 nzs0 bs1 nzs1    = go tAG.zero (bs0 .&. bs1)
  where
    go acc 0        = acc
    go acc bsTodo   = go (tAG.plus acc t) bsTodo'
      where
        b               = lowNzBit bsTodo
        jF              = b64Index b
        t               = f !$ C.index nzs0 (jF bs0) !$ C.index nzs1 (jF bs1)
        bsTodo'         = bsTodo .^. b
{-# SPECIALIZE aDotWith :: AbelianGroup c2 -> (c -> c1 -> c2) -> Word64 -> SmallArray c ->
    Word64 -> SmallArray c1 -> c2 #-}

dotWith         :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr1, C.Element arr1 c1) =>
                    AbelianGroup c2 -> (c -> c1 -> c2) -> VectorA arr c -> VectorA arr1 c1 -> c2
{- ^ @dotWith tAG f@ assumes @f c zero == f zero c == zero@. \(k\) steps, where the input
    vectors have \(k\) common indices. For sparse vectors, \(k\) more precisely must also
    include the number of common nodes in the input trees. -}
dotWith tAG f   = go
  where
    go (SVE bs0 nzs0)     (SVE bs1 nzs1)    = aDotWith tAG f bs0 nzs0 bs1 nzs1
    go x                  y
        | getIW2 x > getIW2 y   = if x.bs .&. 1 /= 0 then go (C.index x.nzts 0) y else tAG.zero
        | getIW2 x < getIW2 y   = if y.bs .&. 1 /= 0 then go x (C.index y.nzts 0) else tAG.zero
    go (SVV bs0 _ nzts0) (SVV bs1 _ nzts1)  = aDotWith tAG go bs0 nzts0 bs1 nzts1
    go _                 _                  = undefined
{-# SPECIALIZE dotWith :: AbelianGroup c2 -> (c -> c1 -> c2) -> Vector c -> Vector c1 -> c2 #-}

timesNzdC       :: (C.Contiguous arr, C.Element arr c) => Ring c -> c -> Op1 (VectorA arr c)
{- ^ the @c@ must not be a right zero divisor, i.e. @a*c = 0 => a = 0@. Usually \(m\) steps, or
    up to \((d - log_{64} m) m\) for a very sparse vector. -}
timesNzdC (Ring { times }) c    = mapNzFC (`times` c)
{-# INLINE timesNzdC #-}

timesNzdCU      :: (Num c, Prim c) => c -> Op1 (VectorU c)
{- ^ 'timesNzdC' over an unboxed type, for speed. -}
timesNzdCU c (SVE bs nzs)       = SVE bs (C.map' (* c) nzs)
timesNzdCU c (SVV bs iW2 nzts)  = SVV bs iW2 (C.map' (timesNzdCU c) nzts)
{-# INLINABLE timesNzdCU #-}

timesC          :: (C.Contiguous arr, C.Element arr c) => Ring c -> c -> Op1 (VectorA arr c)
{- ^ If the @c@ is not a right zero divisor, then 'timesNzdC' is faster. Usually \(m\) steps, or
    up to \((d - log_{64} m) m\) for a very sparse vector. -}
timesC cR@(Ring { times }) c    = mapC cR.isZero (`times` c)
{-# INLINE timesC #-}

monicizeUnit    :: (C.Contiguous arr, C.Element arr c) => Ring c -> Int -> Op1 (VectorA arr c)
{- ^ @(monicizeUnit cR i v)@ requires that the @i@'th coefficient of @v@ is a unit. Usually
    \(m\) steps, or up to \((d - log_{64} m) m\) for a very sparse vector, but checks first
    whether @v@ is already monic. -}
monicizeUnit cR@(Ring { times }) i v    =
    let c       = index cR.zero v i   -- check for c = 1 for speed
    in  if rIsOne cR c then v else mapNzFC (`times` rInv cR c) v
{-# SPECIALIZE monicizeUnit :: Ring c -> Int -> Op1 (Vector c) #-}

aMkModR         :: (C.Contiguous arr, C.Element arr c) =>
                    Ring c -> AbelianGroup (VectorA arr c) -> (c -> Op1 (VectorA arr c)) ->
                    ModR c (VectorA arr c)
aMkModR cR vAG vTimesNzdC   = Module vAG scale vBDiv
  where
    cIsZero         = cR.isZero
    cNzds           = cR.rFlags.noZeroDivisors
    timesNzC        = if cNzds then vTimesNzdC else timesC cR
    scale c v       = if cIsZero c then zero else timesNzC c v
    minusTimesNzC v q w     = vAG.plus v $! timesNzC (cR.neg q) w
    vBDiv doFull v w    = fromMaybe (cR.zero, v) $ do
        i :!: wc    <- toLazy $ headPairMaybe w
        vc          <- if doFull.b then toLazy $ indexMaybe v i else
                        do vi :!: c <- toLazy $ headPairMaybe v; pureIf (vi == i) c
        let (q, _)  = cR.bDiv doFull vc wc
        pureIf (not (cIsZero q)) (q, minusTimesNzC v q w)
{-# SPECIALIZE aMkModR :: Ring c -> AbelianGroup (Vector c) -> (c -> Op1 (Vector c)) ->
    ModR c (Vector c) #-}

mkModR          :: Ring c -> ModR c (Vector c)
-- ^ Make a right module of vectors over a coordinate ring.
mkModR cR       = aMkModR cR (mkAG cR.ag) (timesNzdC cR)

mkModRU         :: (Eq c, Num c, Prim c) => Ring c -> ModR c (VectorU c)
-- ^ 'mkModR' with unboxed coordinates.
mkModRU cR      = aMkModR cR mkAGU timesNzdCU
{-# INLINABLE mkModRU #-}

-- * Permute

{- | A t'Permute' is a permutation, i.e. a bijection from @[0 .. r - 1]@ to @[0 .. r - 1]@ for
    some (non-unique) @r@. It is stored sparsely, with fixpoints omitted. -}
data Permute    = Permute { to :: Vector Int, from :: Vector Int }
    deriving Show;  -- ^ e.g. for testing & debugging

instance Eq Permute where
    p == q          = p.to == q.to

pToF            :: Permute -> Op1 Int
-- ^ Use a permutation as a function. \(d\) steps per function call.
pToF p i        = index i p.to i

pIdent          :: Permute
-- ^ The identity function as a permutation.
pIdent          = Permute zero zero

pSwap           :: Int -> Int -> Permute
-- ^ Transpose (swap) two @Int@s.
pSwap i j       = if i == j then pIdent else Permute v v
  where
    ~v      = fromDistinctNzs [i :!: j, j :!: i]

pCycle          :: [Int] -> Permute
{- ^ Take each element of the list to the next one, and the last element (if the list is
    nonempty) to the first. The elements must be distinct. Other @Int@s are left fixed.
    \(O(n log_2 n)\). -}
pCycle []           = pIdent
pCycle [_]          = pIdent
pCycle ks@(h : t)   = Permute (fromDistinctNzs (S.zip ks rotL))
                              (fromDistinctNzs (S.zip rotL ks))
  where
    rotL    = t ++ [h]

fToP            :: Int -> Op1 Int -> Permute
{- ^ Convert @r@ and a bijection on @[0, 1 .. r - 1]@ to a permutation. Fixpoints (@i@ where
    @f i == i@) are compressed (stored compactly). \(O(r log_2 r)\). -}
fToP r f        = Permute (fromDistinctAscNzs toL) (fromDistinctNzs (map S.swap toL))
  where
    toL             = [i :!: e | i <- [0, 1 .. r - 1], let e = f i, e /= i]

injToPermute    :: Vector Int -> Permute
{- ^ Extend an injective (finite) partial function on [0 ..] to a minimal permutation. The newly
    defined part of the function will be monotonic. -}
injToPermute to0    = Permute to from
  where
    keysAndNot  = keys .* andNot
    to1         = mapCMaybeWithIndex (\i c -> if i /= c then S.Just c else S.Nothing) to0
    from1       = (fromDistinctNzs . map S.swap . toDistinctAscNzs) to1
    is          = keysAndNot to1 from1
    js          = keysAndNot from1 to1
    to          = unionDisj to1   (fromDistinctAscNzs (S.zip js is))
    from        = unionDisj from1 (fromDistinctAscNzs (S.zip is js))

rComposePTo     :: Vector Int -> Vector Int -> Vector Int -> Vector Int
-- Compute (.to) of the right composition of (Permute pTo pFrom) and qTo.
rComposePTo pTo pFrom qTo   = unionWith (== -1) const pTo' qTo
  where
    ic i c      = i :!: (if c == i then -1 else c)
    movesTwice  = fromDistinctNzs (foldLIntersect' (\r i c -> ic i c : r) [] pFrom qTo)
    pTo'        = unionWith (const False) const movesTwice pTo

pCompose        :: Op2 Permute
-- ^ (left) composition of permutations as functions
pCompose (Permute pTo pFrom) (Permute qTo qFrom)    = Permute to from
  where
    to      = rComposePTo qTo qFrom pTo
    from    = rComposePTo pFrom pTo qFrom

pGroup          :: Group Permute
-- ^ The (infinite) group of permutations under (left) composition.
pGroup          = MkMonoid { .. }
  where
    monFlags        = MonoidFlags { nontrivial = True, abelian = False, isGroup = True }
    eq              = (==)
    op              = pCompose
    ident           = pIdent
    isIdent p       = isZero p.to
    inv p           = Permute p.from p.to

permuteV2       :: (C.Contiguous arr, C.Element arr c) =>
                    Vector Int -> VectorA arr c -> [Int :!: c] -> VectorA arr c :!: [Int :!: c]
-- Split @v@ into fixpoints of @to@ and pairs pushed onto @ics@.
permuteV2 (SVE toBs toIs) v@(SVE vBs nzs) ics0              =
    if fixBs == vBs then v :!: ics0 else runST $ do
        fixNzsMut   <- C.new (popCount fixBs)
        let go 0      _  _    ics   = do
                fixNzs      <- C.unsafeFreeze fixNzsMut
                pure (SVE fixBs fixNzs :!: ics)
            go bsTodo vJ fixJ ics
                | toBs .&. b == 0   = do
                    C.write fixNzsMut fixJ c
                    go bsTodo' (vJ + 1) (fixJ + 1) ics
                |   let toJ     = b64Index b toBs
                    = go bsTodo' (vJ + 1) fixJ ((C.index toIs toJ :!: c) : ics)
              where
                b           = lowNzBit bsTodo
                bsTodo'     = bsTodo .^. b
                c           = C.index nzs vJ
        go vBs 0 0 ics0
  where
    fixBs           = vBs .&. complement toBs
permuteV2 (SVV bs iW2 nzts) v ics   | iW2 > getIW2 v        =
    if bs .&. 1 == 0 then v :!: ics else permuteV2 (C.index nzts 0) v ics
permuteV2 to v@(SVV _ iW2 _) ics    | getIW2 to < iW2       =
    permuteV2 (SVV 1 iW2 (C.singleton to)) v ics
permuteV2 (SVV toBs iW2 toNzts) v@(SVV vBs _ vNzts) ics0    =
    if fixBs0 == vBs then v :!: ics0 else runST $ do
        fixNztsMut  <- C.new (popCount vBs)
        let go 0      fixBs _  fixJ ics   = do
                fixNzts     <- unsafeShrinkAndFreeze fixNztsMut fixJ
                pure (svv fixBs iW2 fixNzts :!: ics)
            go bsTodo fixBs vJ fixJ ics
                | toBs .&. b == 0   = do
                    C.write fixNztsMut fixJ vNzt
                    go bsTodo' fixBs vJ' (fixJ + 1) ics
                |   let toJ             = b64Index b toBs
                        v1 :!: ics'     = permuteV2 (C.index toNzts toJ) vNzt ics
                    = if isZero v1 then go bsTodo' fixBs vJ' fixJ ics' else do
                        C.write fixNztsMut fixJ v1
                        go bsTodo' (fixBs .|. b) vJ' (fixJ + 1) ics'
              where
                b           = lowNzBit bsTodo
                bsTodo'     = bsTodo .^. b
                vNzt        = C.index vNzts vJ
                vJ'         = vJ + 1
        go vBs fixBs0 0 0 ics0
  where
    fixBs0          = vBs .&. complement toBs
permuteV2 _ _ _                                             = undefined
{-# SPECIALIZE permuteV2 :: Vector Int -> Vector c -> [Int :!: c] -> Vector c :!: [Int :!: c]
    #-}
{-# INLINEABLE permuteV2 #-}

permuteV        :: (C.Contiguous arr, C.Element arr c) => Permute -> Op1 (VectorA arr c)
{- Permute the coordinates of a vector. For a free module @R^n@, this is the linear map where
    the permutation acts on the standard basis elements. -}
permuteV p v    = unionDisj v1 (fromDistinctNzs ics)
  where
    v1 :!: ics      = permuteV2 p.to v [] 
{-# SPECIALIZE permuteV :: Permute -> Op1 (Vector c) #-}
{-# INLINEABLE permuteV #-}

swap            :: (C.Contiguous arr, C.Element arr c) => Int -> Int -> Op1 (VectorA arr c)
-- ^ swap two coordinates. Up to \(128 d\) steps for a very dense vector.
swap i j        = permuteV (pSwap i j)
{-# SPECIALIZE swap :: Int -> Int -> Op1 (Vector c) #-}

sortPermute     :: (C.Contiguous arr, C.Element arr c) =>
                    Cmp c -> VectorA arr c -> (VectorA arr c, Permute)
{- ^ Sort a vector, and return a permutation on its coordinates to get the sorted result.
    \(O(n log n)\). -}
sortPermute cmp v   = (fromNzs cs, pGroup.inv (injToPermute (fromNzs is)))
  where
    (is, cs)    = S.unzip (sortLBy (cmp `on` S.snd) (toDistinctAscNzs v))
{-# SPECIALIZE sortPermute :: Cmp c -> Vector c -> (Vector c, Permute) #-}

-- * I/O

showPrec        :: (C.Contiguous arr, C.Element arr c) =>
                    ShowPrec Int -> ShowPrec c -> ShowPrec (VectorA arr c)
-- ^ Show a vector with precedence.
showPrec iSP cSP    = sumPT . map termSP . toDistinctAscNzs
  where
    termSP (i :!: c)    = timesPT (cSP c) (iSP i)
