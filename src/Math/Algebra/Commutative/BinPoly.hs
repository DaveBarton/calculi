{-# LANGUAGE Strict #-}

{- |  A 'BinPoly' is a multivariate polynomial over @Z\/2@ modulo @(x^2+x)@ for each variable
    @x@. These correspond bijectively to functions from @(Z\/2)^n@ to @Z/2@. We can reduce any
    monomial to have degree at most 1 in each variable, and the nonzero coefficients are all
    1 mod 2. So we can represent a 'BinPoly' concisely as a sum of nonzero terms, where each
    term can be represented as a binary integer, with each bit giving the degree of the
    corresponding variable in that term. Lexicographic order then corresponds to integer order
    (with more main variables corresponding to more main bits), and multiplication of two terms
    is just a bitwise OR. For graded lex or graded reverse lex order, we should also store the
    total degree of each term.
    
    An ideal of 'BinPoly's corresponds to a polynomial ideal containing all the generators
    @x^2+x@. Note that these generators cannot be represented as 'BinPoly's, so a Groebner Basis
    algorithm must handle them specially. If @p@'s leading term contains the variable @x@, then
    the s-poly of @p@ and @x^2+x@ is @x*p@ \`mod\` @x^2+x@.
    
    This module uses LANGUAGE Strict. In particular, constructor fields and function arguments
    are strict unless marked with a ~.
-}

module Math.Algebra.Commutative.BinPoly (
    EV58, fromBits58, toBits58, totDeg58, evCmp58,
    BinPoly, BPOtherOps(..), bp58Ops, bpCountZeros
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Commutative.GroebnerBasis

import Control.Monad.Extra (pureIf)
import Data.Bits ((.&.), (.|.), bit, complement, countLeadingZeros, popCount, testBit,
    unsafeShiftL, unsafeShiftR)
import Data.Foldable (toList)
import Data.Maybe (catMaybes, fromJust)
import Data.Word (Word64)
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL

import Control.Parallel.Cooperative


newtype EV58        = EV58 { w64 :: Word64 }    deriving Eq

instance Show EV58 where    -- e.g. for testing & debugging
    show v      = show0x v.w64

mask58              :: Word64
mask58              = 0x03FF_FFFF_FFFF_FFFF

high6               :: Word64
high6               = complement mask58

fromBits58          :: Word64 -> EV58
fromBits58 bs       = EV58 (fromIntegral (popCount bs) `unsafeShiftL` 58 .|. bs)

fromBits58Only      :: Word64 -> EV58
fromBits58Only bs   = fromBits58 (bs .&. mask58)

toBits58            :: EV58 -> Word64
toBits58 v          = v.w64 .&. mask58

totDeg58            :: EV58 -> Word
totDeg58 v          = fromIntegral (v.w64 `unsafeShiftR` 58)

lexCmp58            :: Cmp EV58
-- ^ <= 58 variables, lexicographic ordering, lower bits correspond to less main variables
lexCmp58 v w        = compare (toBits58 v) (toBits58 w)

grLexCmp58          :: Cmp EV58
{- ^ <= 58 variables, graded lexicographic ordering, lower bits correspond to less main
    variables -}
grLexCmp58 v w      = compare v.w64 w.w64

grRevLexCmp58       :: Cmp EV58
{- ^ <= 58 variables, graded reverse lexicographic ordering, lower bits correspond to more main
    variables -}
grRevLexCmp58 v w   = compare (v.w64 .&. high6) (w.w64 .&. high6) <> compare w.w64 v.w64

evCmp58             :: StdEvCmp -> Cmp EV58
evCmp58             = \case
    LexCmp      -> lexCmp58
    GrLexCmp    -> grLexCmp58
    GrRevLexCmp -> grRevLexCmp58


type BinPoly ev     = SL.List ev
-- ^ nonzero terms, in decreasing order

instance GBEv EV58 where
    evDivides _nVars v w    = v.w64 .&. mask58 .&. w.w64 == v.w64 .&. mask58
    {-# INLINE evDivides #-}
    evLCM _nVars v w    = fromBits58Only (v.w64 .|. w.w64)
    {-# INLINE evLCM #-}
    evTotDeg            = totDeg58

instance GBPoly EV58 EV58 (BinPoly EV58) where
    leadEvNz (ev :! _)  = ev
    leadEvNz SL.Nil     = undefined
    {-# INLINE leadEvNz #-}

{-# SPECIALIZE gbiSmOps :: GBPolyOps EV58 (BinPoly EV58) ->
    SubmoduleOps (BinPoly EV58) (BinPoly EV58) (GroebnerIdeal (BinPoly EV58)) #-}

-- | For Boolean logic, we treat 1 as True and 0 as False.
data BPOtherOps ev vals     = BPOtherOps {
    nVars           :: Int,
    evMainBit       :: Op1 ev,              -- ^ main bit only, or 0 if none
    evAt            :: ev -> vals -> Bool,
    bpNot           :: Op1 (BinPoly ev),    -- ^ @bpNot x == x + 1@
    (∧)             :: Op2 (BinPoly ev),    -- ^ \"and\", same as multiplication
    (∨)             :: Op2 (BinPoly ev),    -- ^ \"or\", @x ∨ y = x + y + xy = (x+1)(y+1) + 1@
    pAt             :: BinPoly ev -> vals -> Bool,
    pParse          :: Parser (BinPoly ev)
}

bpSortCancel            :: Cmp ev -> SL.List ev -> BinPoly ev
bpSortCancel evCmp evs  = cancelRev (sortLBy evCmp (SL.toListReversed evs)) SL.Nil
  where
    cancelRev (v : t1@(w : ~t2)) r
        | evCmp v w == EQ   = cancelRev t2 r
        | otherwise         = cancelRev t1 (v :! r)
    cancelRev [v] r         = v :! r
    cancelRev [] r          = r

bp58Ops                         :: Cmp EV58 -> IsGraded -> [Text] -> UseSugar ->
                                    (GBPolyOps EV58 (BinPoly EV58), BPOtherOps EV58 Word64)
-- ^ In @bp58Ops evCmp isGraded descVarTs useSugar@, @descVarTs@ lists more main variables
-- first, and each variable name must be a legal identifier name.
bp58Ops evCmp isGraded descVarTs useSugar   = assert (nVars <= 58)
    (GBPolyOps { monicizeU = id, .. }, BPOtherOps { .. })
  where
    nVars               = length descVarTs
    
    evOne               = EV58 0
    evTimes             = evLCM nVars
    evMaybeQuo          :: EV58 -> EV58 -> Maybe EV58
    evMaybeQuo v w      = pureIf (evDivides nVars w v) (fromBits58Only (v.w64 - w.w64))
    n4s                 = quot (nVars + 3) 4
    nEvGroups           = n4s * max (n4s - 1) 1
    evGroup v           = reverse [5 * pc4 i + pc4 j
                            | i <- [0 .. n4s - 1], j <- [0 .. n4s - 1], i /= j || n4s == 1]
      where
        bs          = toBits58 v
        pc4 k       = fromIntegral (popCount (bs .&. (0xF `unsafeShiftL` (4 * k))))
    isRev               = nVars > 1 && evCmp (fromBits58 1) (fromBits58 2) == GT
    varBitJsDesc        =   -- most main first
        (if isRev then id else reverse) [0 .. nVars - 1]
    evShowPrec w        = productPT (map (PrecText AtomPrec) (catMaybes mVarTs))
      where
        mVarTs      = zipWith (pureIf . testBit w.w64) varBitJsDesc descVarTs
    
    bpPlus              = go SL.Nil
      where
        go r xs@(x :! ~t) ys@(y :! ~u)  =
            case x `evCmp` y of
                GT  -> go (x :! r) t  ys
                LT  -> go (y :! r) xs u
                EQ  -> go r        t  u
        go r xs           SL.Nil        = SL.prependReversed r xs
        go r SL.Nil       ys            = SL.prependReversed r ys
    bpAG                = AbelianGroup (agFlags (IsNontrivial True)) (==) bpPlus SL.Nil null id
    bpRFlags            =
        RingFlags { commutative = True, noZeroDivisors = False, nzInverses = False }
    bpFromZ n           = if even (n :: Integer) then SL.Nil else SL.singleton evOne
    bpTimesEv bp ev     = if ev == evOne then bp else   -- for speed
        let (rts, rfs)      = SL.partitionReversed (evDivides nVars ev) bp  -- for speed
        in  bpPlus (SL.reverse rts) (bpSortCancel evCmp (fmap (evTimes ev) rfs))
    bpTimes vs ws       = bpSortCancel evCmp (SL.explodeReversed (\w -> fmap (evTimes w) vs) ws)
    bpDiv  doFull x (w :! u)    = go SL.Nil SL.Nil x
      where
        go qRev rRev (v :! t)
            | Just qv   <- evMaybeQuo v w           =
                go (qv :! qRev) rRev (t `bpPlus` bpTimesEv u qv)
            | doFull.b && evCmp v w == GT  = go qRev (v :! rRev) t
        go qRev rRev r                          = (SL.reverse qRev, SL.prependReversed rRev r)
    bpDiv _doFull x SL.Nil      = (SL.Nil, x)
    pR                  = Ring bpAG bpRFlags bpTimes (bpFromZ 1) bpFromZ bpDiv
    evBit i             = EV58 (0x0400_0000_0000_0000 .|. bit i)    -- single bit
    descVarPs           = map (SL.singleton . evBit) varBitJsDesc
    
    varBitJsAsc         = reverse varBitJsDesc
    extraSPairs v j h   = [SPair (i - nVars) j (h + 1) v (spCmp evCmp useSugar)
                            | i <- varBitJsAsc, testBit v.w64 i]
    sPoly _f g (SPair { i })    | i < 0     = g `bpTimesEv` fromBits58 (bit (i + nVars))
    sPoly  f g (SPair { m })                = mult1 f `bpPlus` mult1 g
      where
        mult1 (v :! t)      = bpTimesEv t (fromJust (evMaybeQuo m v))
        mult1 _             = undefined
    homogDeg0           = if isGraded.b then SL.match 0 (\v _ -> evTotDeg v) else
        foldl' (\d v -> max d (evTotDeg v)) 0
    pShowPrec           = sumPT . map evShowPrec . toList
    
    evMainBit (EV58 w)  | isRev     = fromBits58 (w .&. (- w))
    evMainBit (EV58 0)              = EV58 0
    evMainBit v                     = evBit (63 - countLeadingZeros (toBits58 v))
    evAt v bs           = v.w64 .&. bs == v.w64 .&. mask58
    pOne                = pR.one
    bpNot               = bpPlus pOne
    (∧)                 = pR.times
    x ∨ y               = bpNot (bpNot x ∧ bpNot y)
    pAt p bs            = foldl' (\b v -> b /= evAt v bs) False p
    pParse              = zzGensRingParse pR (varParse descVarTs descVarPs)

bpCountZeros        :: BPOtherOps EV58 Word64 -> [BinPoly EV58] -> Int
-- ^ @1 <= nVars <= 58@; fastest if the first polynomials are short or have few zeros
bpCountZeros (BPOtherOps { nVars, pAt }) ps     =
    assert (nVars > 0) $ forkJoinPar (split (1 `unsafeShiftL` (nVars - 1))) sum (go maxUni) 0
  where
    go 0 bs     = if any (`pAt` bs) ps then 0 else 1
    go b bs     = go b1 bs + go b1 (bs .|. b)
      where
        b1  = b `unsafeShiftR` 1
    maxUni      = 1 `unsafeShiftL` min (nVars - 1) 12
    split b bs  | b == maxUni   = [bs]
    split b bs  = split b1 bs ++ split b1 (bs .|. b)
      where
        b1  = b `unsafeShiftR` 1
