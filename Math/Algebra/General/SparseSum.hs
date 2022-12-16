{-# LANGUAGE Strict #-}

{- |  A 'SparseSum' is a linear combination where zero terms are omitted.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.General.SparseSum (
    SparseSum(..), SparseSumUniv,
    ssIsZero, ssDegNZ, ssHeadCoef, ssTail, ssLeadTerm,
    ssLexCmp, ssDegCmp,
    ssLead, ssMapC, ssMapNZFC, ssShift, ssShiftMapC, ssShiftMapNZFC, ssFoldr,
    ssRTails, ssForceTails, ssNumTerms,
    ssAGUniv, ssDotWith,
    ssNZCTimes, ssCTimes, ssMonicize, ssTimesNZC, ssTimesC, ssTimesNZMonom, ssTimesMonom,
        ssTimes,
    ssShowPrec
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category


data SparseSum c d  = SSNZ c d {- @@@ ~ -} (SparseSum c d) | SSZero
    deriving (Eq, Show)     -- e.g. for testing & debugging
-- ^ a sorted list of non-\"zero\" terms, with \"degrees\" decreasing according to a total order

type SparseSumUniv d c  = UnivL AbelianGroup (TgtArrsF (->) c d) (->) (SparseSum c d)
{- ^ an @AbelianGroup (SparseSum c d)@, @dcToSS@ function, and a function for mapping to other
    'AbelianGroup's @t@ that have a @d -> Hom_AG(c, t)@; \(⊕↙d C_d\) where each \(C_d\) is a
    copy of \(C\). -}


ssIsZero                :: SparseSum c d -> Bool
ssIsZero SSZero         = True
ssIsZero _              = False

ssDegNZ                 :: SparseSum c d -> d
ssDegNZ (SSNZ _ d _)    = d
ssDegNZ SSZero          = undefined

ssHeadCoef              :: SparseSum c d -> c
ssHeadCoef (SSNZ c _ _) = c
ssHeadCoef SSZero       = undefined

ssTail                  :: SparseSum c d -> SparseSum c d
ssTail (SSNZ _ _ t)     = t
ssTail SSZero           = undefined

ssLeadTerm              :: Op1 (SparseSum c d)
ssLeadTerm SSZero       = SSZero
ssLeadTerm (SSNZ c d _) = SSNZ c d SSZero

ssLexCmp        :: Cmp d -> c -> Cmp c -> Cmp (SparseSum c d)
-- ^ \"lexicographic\" comparison
ssLexCmp dCmp cZero cCmp        = ssCmp where
    ssCmp s t
        | ssIsZero s && ssIsZero t      = EQ
        | ssIsZero t || not (ssIsZero s) && ssDegNZ s `dCmp` ssDegNZ t == GT    =
            let rel = ssHeadCoef s `cCmp` cZero
            in  if rel /= EQ then rel else ssCmp (ssTail s) t
        | ssIsZero s || ssDegNZ s `dCmp` ssDegNZ t == LT    =
            let rel = cZero `cCmp` ssHeadCoef t
            in  if rel /= EQ then rel else ssCmp s (ssTail t)
        | otherwise     =
            let rel = ssHeadCoef s `cCmp` ssHeadCoef t
            in  if rel /= EQ then rel else ssCmp (ssTail s) (ssTail t)

ssDegCmp        :: Cmp d -> Bool -> Cmp (SparseSum c d)
ssDegCmp dCmp deep s t
    | ssIsZero s        = if ssIsZero t then EQ else LT
    | ssIsZero t        = GT
    | otherwise         =
        let ord = dCmp (ssDegNZ s) (ssDegNZ t)
        in  if ord /= EQ || not deep then ord else ssDegCmp dCmp deep (ssTail s) (ssTail t)

ssLead          :: Pred c -> c -> d -> SparseSum c d -> SparseSum c d
-- ^ @ssLead cIs0 c d s@ assumes @d > degree(s)@
ssLead cIs0 c d ~t      = if cIs0 c then t else SSNZ c d t

ssMapC          :: Pred c' -> (c -> c') -> SparseSum c d -> SparseSum c' d
ssMapC _   _ SSZero         = SSZero
ssMapC is0 f (SSNZ c d ~t)  =
    let c'      = f c
        ~t'     = ssMapC is0 f t
    in  if is0 c' then t' else SSNZ c' d t'

ssMapNZFC       :: (c -> c') -> SparseSum c d -> SparseSum c' d
-- ^ assumes the @(c -> c')@ takes nonzero values to nonzero values
ssMapNZFC _ SSZero          = SSZero
ssMapNZFC f (SSNZ c d ~t)   = SSNZ (f c) d (ssMapNZFC f t)

ssShift         :: (d -> d') -> SparseSum c d -> SparseSum c d'
-- ^ assumes the @(d -> d')@ is order-preserving
ssShift _ SSZero        = SSZero
ssShift f (SSNZ c d ~t) = SSNZ c (f d) (ssShift f t)

ssShiftMapC     :: Pred c' -> (d -> d') -> (c -> c') -> SparseSum c d -> SparseSum c' d'
-- ^ assumes the @(d -> d')@ is order-preserving
ssShiftMapC is0 df cf     = go
  where
    go SSZero           = SSZero
    go (SSNZ c d ~t)    =
        let c'  = cf c
            ~t' = go t
        in  if is0 c' then t' else SSNZ c' (df d) t'

ssShiftMapNZFC  :: (d -> d') -> (c -> c') -> SparseSum c d -> SparseSum c' d'
{- ^ assumes the @(d -> d')@ is order-preserving, and the @(c -> c')@ takes nonzero values to
    nonzero values -}
ssShiftMapNZFC _  _  SSZero         = SSZero
ssShiftMapNZFC df cf (SSNZ c d ~t)  = SSNZ (cf c) (df d) (ssShiftMapNZFC df cf t)

ssFoldr         :: (c -> d -> t -> t) -> t -> SparseSum c d -> t
ssFoldr f t     = go
  where
    go SSZero           = t
    go (SSNZ c d ~r)    = f c d (go r)

ssRTails                :: SparseSum c d -> ()  -- @@ change to rnf and instance NFData !?
ssRTails SSZero         = ()
ssRTails (SSNZ _c _d t) = ssRTails t `seq` ()   -- @@ rnf c and d also!?

ssForceTails            :: Op1 (SparseSum c d)
ssForceTails x          = ssRTails x `seq` x

ssNumTerms      :: SparseSum c d -> Int
ssNumTerms      = ssFoldr (\ _ _ t -> t + 1) 0

ssAGUniv        :: forall c d. IAbelianGroup c => Cmp d -> SparseSumUniv d c
ssAGUniv dCmp   = UnivL ssAG (TgtArrsF dcToSS) univF
  where
    ssLead'     = ssLead (isZero @c)
    -- {-# SCC ssPlus #-}
    ssPlus      :: Op2 (SparseSum c d)
    ssPlus SSZero          t                    = t
    ssPlus s               SSZero               = s
    ssPlus s@(SSNZ c d ~r) t@(SSNZ c' d' ~r')   =   -- {-# SCC ssPlusNZ #-}
        case d `dCmp` d' of
            GT -> SSNZ c  d  (r `ssPlus` t)
            LT -> SSNZ c' d' (s `ssPlus` r')
            EQ -> ssLead' (c +. c') d (r `ssPlus` r')
    ssNeg       :: Op1 (SparseSum c d)
    ssNeg SSZero        = SSZero
    ssNeg (SSNZ c d ~t) = SSNZ (neg c) d (ssNeg t)
    ssEq        :: EqRel (SparseSum c d)
    ssEq SSZero SSZero  = True
    ssEq SSZero _       = False
    ssEq _      SSZero  = False
    ssEq (SSNZ c d ~r) (SSNZ c' d' ~r')     = dCmp d d' == EQ && c ==. c' && ssEq r r'
    ssAG        = Group agFlags ssEq ssPlus SSZero ssIsZero ssNeg
    dcToSS d c  = ssLead' c d SSZero
    univF (Group _ _ vPlus vZero _ _) (TgtArrsF dcToV)  = go
      where
        go SSZero       = vZero
        go (SSNZ c d t) = vPlus !$ dcToV d c !$ go t

ssDotWith       :: IAbelianGroup c2 => Cmp d -> (c -> c1 -> c2) ->
                        SparseSum c d -> SparseSum c1 d -> c2
ssDotWith dCmp f    = dot where
    dot s t     = if ssIsZero s || ssIsZero t then zero else
        let d = ssDegNZ s
            e = ssDegNZ t
        in case d `dCmp` e of
            GT -> dot (ssTail s) t
            LT -> dot s (ssTail t)
            EQ -> (+.) !$ (f !$ ssHeadCoef s !$ ssHeadCoef t) !$ dot (ssTail s) (ssTail t)

ssNZCTimes      :: forall c d. IRing c => c -> Op1 (SparseSum c d)
-- ^ the @c@ is nonzero
ssNZCTimes
    | hasEIBit (iRFlags @c) NoZeroDivisors  = \c -> ssMapNZFC (c *.)
    | otherwise                             = \c -> ssMapC isZero (c *.)

ssCTimes        :: IRing c => c -> Op1 (SparseSum c d)
ssCTimes c s    = if isZero c then SSZero else ssNZCTimes c s

ssMonicize      :: IRing c => Op1 (SparseSum c d)
-- ^ @(ssMonicize s)@ requires that @s@ is nonzero, and its leading coefficient is a unit
ssMonicize s    = ssMapNZFC (rInv (ssHeadCoef s) *.) s

ssTimesNZC      :: forall c d. IRing c => c -> Op1 (SparseSum c d)
-- ^ the @c@ is nonzero
ssTimesNZC
    | hasEIBit (iRFlags @c) NoZeroDivisors  = \c -> ssMapNZFC (*. c)
    | otherwise                             = \c -> ssMapC isZero (*. c)

ssTimesC        :: IRing c => c -> Op1 (SparseSum c d)
ssTimesC c s    = if isZero c then SSZero else ssTimesNZC c s

ssTimesNZMonom  :: forall c d. IRing c => Op2 d -> SparseSum c d -> d -> c -> SparseSum c d
-- ^ assumes the @Op2 d@ is order-preserving in each argument, and the @c@ is nonzero
ssTimesNZMonom dOp2
    | hasEIBit (iRFlags @c) NoZeroDivisors  = \s d c -> ssShiftMapNZFC (`dOp2` d) (*. c) s
    | otherwise                             = \s d c -> ssShiftMapC isZero (`dOp2` d) (*. c) s

ssTimesMonom    :: IRing c => Op2 d -> SparseSum c d -> d -> c -> SparseSum c d
-- ^ assumes the @Op2 d@ is order-preserving in each argument
ssTimesMonom dOp2 s d c     = if isZero c then SSZero else ssTimesNZMonom dOp2 s d c

ssTimes         :: IRing c => SparseSumUniv d c -> Op2 d -> Op2 (SparseSum c d)
-- ^ assumes the @Op2 d@ is order-preserving in each argument
ssTimes (UnivL ssAG _ univF) dOp2 s     = univF ssAG (TgtArrsF (sToTimesDC s))
  where
    sToTimesDC      = ssTimesNZMonom dOp2


ssShowPrec      :: ShowPrec d -> ShowPrec c -> ShowPrec (SparseSum c d)
ssShowPrec dSP cSP prec x   =
    let s = ssFoldr (\ c d st -> plusS (timesS (cSP multPrec c) (dSP multPrec d)) st) "0" x
    in  if prec > addPrec && not (ssIsZero x) && not (ssIsZero (ssTail x)) || prec > multPrec
            then '(':s++")" else s
