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
    zero, fromPIC, fromIMaybeC, fromNzIC, fromDistinctAscNzs,
    -- * Modify/Permute
    vApply, invPermute, swap,
    -- * Split/Join
    split, join,
    -- * Query
    isZero, index, indexMaybe, size, headPairMaybe, headPair, lastPairMaybe, lastPair,
    -- * Map
    mapC, mapNzFC, mapCMaybeWithIndex,
    -- * Fold
    foldBIMap', iFoldR, iFoldL, toDistinctAscNzs,
    -- * Addition
    unionWith, plusU, mkAG,
    -- * Multiplication
    dotWith, timesNzdC, timesNzdCU, timesC, monicizeUnit,
    -- * I/O
    showPrec
) where

import Math.Algebra.General.Algebra

import Control.Monad.ST (ST, runST)
import Control.Parallel.Cooperative (fbTruncLog2, lowNzBit)
import Data.Bits ((.&.), (.|.), (.^.), (!<<.), (!>>.), countTrailingZeros, finiteBitSize,
    popCount)   -- @@ is countLeadingZeros faster on ARM?
import Data.Functor.Classes (liftEq)
import Data.Mod.Word (Mod)
import qualified Data.Primitive.Contiguous as C
import Data.Primitive.PrimArray (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import Data.Primitive.Types (Prim)
import qualified Data.Strict.Maybe as S
import qualified Data.Strict.Tuple as S
import Data.Strict.Tuple ((:!:), pattern (:!:))
import Data.Word (Word64)
import Fmt ((+|), (|+))
import GHC.TypeNats (KnownNat)


nothingIf       :: Pred a -> a -> S.Maybe a     -- move and export?
nothingIf p a   = if p a then S.Nothing else S.Just a


b64             :: Int -> Word64    -- unsafe 'bit'; 0 <= i < 64
b64 i           = 1 !<<. i

b64Index        :: Word64 -> Word64 -> Int  -- b is a bit; position in nonzero bits or -1
b64Index b bs   = if b .&. bs == 0 then -1 else popCount ((b - 1) .&. bs)


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

aCheck          :: (C.Contiguous arr, C.Element arr c) => Pred c -> Word64 -> arr c -> [Text]
aCheck cIsZero bs64 nzs     =
       ["Lengths don't match: "+|nBs|+" and "+|nNzs|+"" | nBs /= nNzs]
    ++ [""+|nZs|+" zero elements" | nZs > 0]
  where
    nBs     = popCount bs64
    nNzs    = C.size nzs
    nZs     = C.foldl' (\n c -> if cIsZero c then n + 1 else n) (0 :: Int) nzs

check           :: (C.Contiguous arr, C.Element arr c) => Pred c -> VectorA arr c -> [Text]
{- ^ (Only needed for testing.) Check the integrity (internal invariants) of a vector, given a
    @cIsZero@ predicate, and return a list of errors. The integrity of the individual
    coordinates is not checked. -}
check cIsZero   = go (finiteBitSize (0 :: Int))
  where
    go _     (SVE bs nzs)       = aCheck cIsZero bs nzs
    go parW2 (SVV bs iW2 nzts)  =
           ["iW2 too big: "+|iW2|+" >= "+|parW2|+"" | iW2 >= parW2]
        ++ ["iW2 illegal: "+|iW2|+""                | iW2 < 6 || iW2 `rem` 6 /= 0]
        ++ aCheck isZero bs nzts
        ++ ["bs <= 1: "+|show0x bs|+""              | bs <= 1]
        ++ foldMap (go iW2) nzts

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
    (Word64 -> SmallArray (VectorA arr0 c0) -> Word64 -> SmallArray (VectorA arr1 c1) ->
        Word64 :!: SmallArray (VectorA arr2 c2)) ->
    VectorA arr0 c0 -> VectorA arr1 c1 -> VectorA arr2 c2
{- For speed, the caller may want to check isZero, or getIW2 x < or > getIW2 y. Else note svvF
    may be passed an unnormalized argument. -}
combineSv sveF svvF     = go
  where
    go (SVE bs0 nzs0) (SVE bs1 nzs1)    = S.uncurry SVE $ sveF bs0 nzs0 bs1 nzs1
    go x y
        | getIW2 x > getIW2 y           = go x (SVV 1 (getIW2 y + 6) (C.singleton y))
        | getIW2 x < getIW2 y           = go (SVV 1 (getIW2 x + 6) (C.singleton x)) y
    go (SVV bs0 iW2 nzts0) (SVV bs1 _ nzts1)    = svv bs2 iW2 nzts2
      where
        bs2 :!: nzts2   = svvF bs0 nzts0 bs1 nzts1
    go _ _                              = undefined

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

fromDistinctAscNzs  :: forall arr c. (C.Contiguous arr, C.Element arr c) =>
                        [Int :!: c] -> VectorA arr c
{- ^ The 'Int's must be distinct and ascending, and the @c@s must be nonzero. Usually \(n\)
    steps, though up to \((d - log_{64} n) n\) if the vector is very sparse. -}
fromDistinctAscNzs []                   = zero
fromDistinctAscNzs ((i0 :!: c0) : t0)   = runST $ do
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
{-# SPECIALIZE fromDistinctAscNzs :: [Int :!: c] -> Vector c #-}

-- * Modify/Permute

aVApply         :: (C.Contiguous dArr, C.Element dArr d, C.Contiguous cArr, C.Element cArr c) =>
                    (d -> Op1 (S.Maybe c)) -> Word64 -> dArr d -> Word64 -> cArr c ->
                    Word64 :!: cArr c
aVApply f bs0 nzs0 bs1 nzs1     = runST $ do
    let bsAll   = bs0 .|. bs1
    nzs2        <- C.new (popCount bsAll)
    let go 0      bs2 _  _  i2  = (bs2 :!: ) <$> unsafeShrinkAndFreeze nzs2 i2
        go bsTodo bs2 i0 i1 i2
            | bs0 .&. b == 0        = do
                C.write nzs2 i2 $! C.index nzs1 i1
                go bsTodo' bs2 i0 (i1 + 1) (i2 + 1)
            | bs1 .&. b == 0        = goD S.Nothing i1
            | otherwise             = goD (S.Just (C.index nzs1 i1)) (i1 + 1)
          where
            b               = lowNzBit bsTodo
            bsTodo'         = bsTodo .^. b
            goD mc1 i1'     = do
                let mc          = f !$ C.index nzs0 i0 !$ mc1
                case mc of
                    S.Nothing       -> go bsTodo' (bs2 .^. b) (i0 + 1) i1' i2
                    S.Just c        -> do
                        C.write nzs2 i2 c
                        go bsTodo' bs2 (i0 + 1) i1' (i2 + 1)
    go bsAll bsAll 0 0 0
{-# SPECIALIZE aVApply :: (d -> Op1 (S.Maybe c)) -> Word64 -> SmallArray d ->
    Word64 -> SmallArray c -> Word64 :!: SmallArray c #-}

vApply          :: (C.Contiguous dArr, C.Element dArr d, C.Contiguous cArr, C.Element cArr c) =>
                    (d -> Op1 (S.Maybe c)) -> VectorA dArr d -> Op1 (VectorA cArr c)
{- ^ @vApply f ds v@ applies @f ds[i]@ to @v[i]@, for each non-missing element in @ds@.
    Usually \(m + n\) steps, though \(m\) if the input trees have few common nodes, or up to
    \(64 (d - log_{64} m) m\) if the first input is very sparse and the second input is very
    dense. -}
vApply f ds0 v0     = fromMaybeSv $ go ds0 (toMaybeSv v0)
  where
    go ds mv
        | S.Nothing <- mv   = toMaybeSv $ mapCMaybeWithIndex (\_i d -> f d S.Nothing) ds
        | isZero ds         = mv
        | S.Just v  <- mv   = toMaybeSv $ combineSv (aVApply f) (aVApply go) ds v
{-# SPECIALIZE vApply :: (d -> Op1 (S.Maybe c)) -> Vector d -> Op1 (Vector c) #-}

invPermute      :: (C.Contiguous jArr, C.Element jArr Int, C.Contiguous arr, C.Element arr c) =>
                    VectorA jArr Int -> Op1 (VectorA arr c)
{- ^ @invPermute js v@ applies the inverse of the sparse permutation @js@, moving each
    @v[js[i]]@ to index @i@ in the result. If @js[i]@ is missing in @js@, then @v[i]@ is used.
    Thus the result is the same as @vApply (\j _ -> indexMaybe v j) js v@. \(d m\) steps if @js@
    is dense, or up to \(d m + 64 (d - log_{64} m) m\) steps if @js@ is very sparse and @v@ is
    very dense. -}
invPermute js v     = vApply (\j _ -> indexMaybe v j) js v
{-# SPECIALIZE invPermute :: Vector Int -> Op1 (Vector c) #-}

swap            :: (C.Contiguous arr, C.Element arr c) => Int -> Int -> Op1 (VectorA arr c)
-- ^ swap two coordinates. Up to \(128 d\) steps for a very dense vector.
swap i j
    | i < j     = invPermute (fromDistinctAscNzs [i :!: j, j :!: i] :: Vector Int)
    | i > j     = swap j i
    | otherwise = id
{-# SPECIALIZE swap :: Int -> Int -> Op1 (Vector c) #-}

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

join            :: (C.Contiguous arr, C.Element arr c) => Op2 (VectorA arr c)
{- ^ Concatenate two vectors, e.g. undoing a 'split'. The indices in the first must be smaller
    than the indices in the second. Up to \(64 d\) steps for a dense vector, or fewer if the
    parts were split at a multiple of a high power of 2. -}
join            = unionWith (const False) (\_ _ -> error "SV.join: Non-disjoint vectors")
{-# SPECIALIZE join :: Op2 (Vector c) #-}

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
    go (SVE bs nzs) i       = if i > 63 || j == -1 then S.Nothing else S.Just (C.index nzs j)
      where
        ~j          = b64Index (b64 i) bs
    go (SVV bs iW2 nzts) i  = if i0 > 63 || j == -1 then S.Nothing else
        go (C.index nzts j) (i .&. ((1 !<<. iW2) - 1))
      where
        i0          = i !>>. iW2
        ~j          = b64Index (b64 i0) bs
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

-- * Map

aMapC           :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c') =>
                    Pred c' -> (c -> c') -> Word64 -> arr c -> Word64 :!: arr' c'
-- assumes @popCount bs == C.size nzs@
aMapC is0 f bs nzs    = assert (popCount bs == C.size nzs) $ runST $ do
    nzs'    <- C.new (C.size nzs)
    let go 0      bs' _ j'  = (bs' :!: ) <$> unsafeShrinkAndFreeze nzs' j'
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

aMapCWithIndex  :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c') =>
                    (Int -> c -> S.Maybe c') -> Int -> Int -> Word64 -> arr c ->
                    Word64 :!: arr' c'
aMapCWithIndex f start iW2 bs nzs   = assert (popCount bs == C.size nzs) $ runST $ do
    nzs'    <- C.new (C.size nzs)
    let go 0      bs' _ j'  = (bs' :!: ) <$> unsafeShrinkAndFreeze nzs' j'
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
{-# SPECIALIZE aMapCWithIndex :: (Int -> c -> S.Maybe c') -> Int -> Int ->
                    Word64 -> SmallArray c -> Word64 :!: SmallArray c' #-}

mapCMaybeWithIndex  :: (C.Contiguous arr, C.Element arr c, C.Contiguous arr', C.Element arr' c')
                        => (Int -> c -> S.Maybe c') -> VectorA arr c -> VectorA arr' c'
{- ^ @mapCMaybeWithIndex f@ assumes @f i zero@ is zero, for all @i@. Usually \(m\) steps, or up
    to \((d - log_{64} m) m\) for a very sparse vector. -}
mapCMaybeWithIndex f    = fromMaybeSv . go 0
  where
    go start (SVE bs nzs)       = toMaybeSv $ SVE bs' nzs'
      where
        bs' :!: nzs'    = aMapCWithIndex f start 0 bs nzs
    go start (SVV bs iW2 nzts)  = toMaybeSv $ svv bs' iW2 nzts'
      where
        bs' :!: nzts'   = aMapCWithIndex go start iW2 bs nzts
{-# SPECIALIZE mapCMaybeWithIndex :: (Int -> c -> S.Maybe c') -> Vector c -> Vector c' #-}

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

toDistinctAscNzs    :: (C.Contiguous arr, C.Element arr c) => VectorA arr c -> [Int :!: c]
-- ^ @toDistinctAscNzs = iFoldR (\i c -> ((i :!: c) :)) []@. \(m\) steps.
toDistinctAscNzs    = iFoldR (\i c -> ((i :!: c) :)) []
{-# SPECIALIZE toDistinctAscNzs :: Vector c -> [Int :!: c] #-}

-- * Addition

aUnionWith      :: (C.Contiguous arr, C.Element arr c) => Pred c -> Op2 c ->
                    Word64 -> arr c -> Word64 -> arr c -> Word64 :!: arr c
-- assumes @f c zero == f zero c == c@ and
-- @popCount bs0 == C.size nzs0 && popCount bs1 == C.size nzs1@
aUnionWith _   _ bs0 nzs0 bs1 nzs1  -- to make SV.join fast
    | bs0 < lowNzBit bs1            = bs0 .|. bs1 :!: C.append nzs0 nzs1
aUnionWith is0 f bs0 nzs0 bs1 nzs1  = runST $ do
    let bsAll   = bs0 .|. bs1
    nzs2        <- C.new (popCount bsAll)
    let go 0      bs2 _  _  j2  = (bs2 :!: ) <$> unsafeShrinkAndFreeze nzs2 j2
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
    let go 0      bs2 _  _  j2  = (bs2 :!: ) <$> unsafeShrinkAndFreeze nzs2 j2
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
{-# SPECIALIZE aPlusU :: KnownNat m => Word64 -> PrimArray (Mod m) ->
    Word64 -> PrimArray (Mod m) -> Word64 :!: PrimArray (Mod m) #-}
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
{-# SPECIALIZE plusU :: KnownNat m => Op2 (VectorU (Mod m)) #-}
{-# INLINABLE plusU #-}

mkAG            :: (C.Contiguous arr, C.Element arr c) =>
                    AbelianGroup c -> AbelianGroup (VectorA arr c)
-- ^ Addition of vectors takes the same time as 'unionWith'.
mkAG ag         = AbelianGroup svFlags svEq svPlus zero isZero (mapNzFC ag.neg)
  where
    svEq (SVE bs nzs)      (SVE bs' nzs')           =
        bs == bs' && (C.foldrZipWith (\c c' ~b -> ag.eq c c' && b) True nzs nzs')
    svEq (SVV bs iW2 nzts) (SVV bs' iW2' nzts')     =
        bs == bs' && iW2 == iW2' && liftEq svEq nzts nzts'
    svEq _                 _                        = False
    
    svPlus          = unionWith ag.isZero ag.plus
    svFlags         = agFlags (IsNontrivial ag.monFlags.nontrivial)
{-# SPECIALIZE mkAG :: AbelianGroup c -> AbelianGroup (Vector c) #-}

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
        j bs            = popCount ((b - 1) .&. bs)
        t               = f !$ C.index nzs0 (j bs0) !$ C.index nzs1 (j bs1)
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
        | getIW2 x > getIW2 y   = go (C.index x.nzts 0) y
        | getIW2 x < getIW2 y   = go x (C.index y.nzts 0)
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

-- * I/O

showPrec        :: (C.Contiguous arr, C.Element arr c) =>
                    ShowPrec Int -> ShowPrec c -> ShowPrec (VectorA arr c)
-- ^ Show a vector with precedence.
showPrec iSP cSP    = sumPT . map termSP . toDistinctAscNzs
  where
    termSP (i :!: c)    = timesPT (cSP c) (iSP i)
