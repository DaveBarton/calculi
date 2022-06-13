{-# LANGUAGE ScopedTypeVariables, Strict #-}

{- |  A 'SparseSum' is a linear combination where zero terms are omitted.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.General.SparseSum {- @@() -} where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category


data SparseSum c d  = SSZero | SSNZ c d ~(SparseSum c d)
-- ^ a sorted list of non-\"zero\" terms, with \"degrees\" decreasing according to a total order

type SparseSumUniv d c  = UnivL AbelianGroup (TgtArrsF (->) c d) (->) (SparseSum c d)
-- ^ an @AbelianGroup (SparseSum c d)@, @dc2ss@ function, and a function for mapping to other
-- 'AbelianGroup's that have a @d -> Hom_AG(c, t)@; \(⊕↙d C_d\) where each \(C_d\) is a copy of
-- \(C\).


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

ssNumTerms      :: (SparseSum c d) -> Int
ssNumTerms      = ssFoldr (\ _ _ t -> t + 1) 0

ssAGUniv        :: forall c d. Cmp d -> AbelianGroup c -> SparseSumUniv d c
ssAGUniv dCmp cAG@(Group cEq cPlus _ _cIsZero cNeg)      = UnivL ssAG (TgtArrsF dc2ss) univF
  where
    ssLead'     = ssLead (isZero cAG)
    -- {-# SCC ssPlus #-}
    ssPlus      :: Op2 (SparseSum c d)
    ssPlus SSZero          t                    = t
    ssPlus s               SSZero               = s
    ssPlus s@(SSNZ c d ~r) t@(SSNZ c' d' ~r')   =   -- {-# SCC ssPlusNZ #-}
        case d `dCmp` d' of
            GT -> SSNZ c  d  (r `ssPlus` t)
            LT -> SSNZ c' d' (s `ssPlus` r')
            EQ -> ssLead' (cPlus !$ c !$ c') d (r `ssPlus` r')
    ssNeg       :: Op1 (SparseSum c d)
    ssNeg SSZero        = SSZero
    ssNeg (SSNZ c d ~t) = SSNZ (cNeg c) d (ssNeg t)
    ssEq        :: EqRel (SparseSum c d)
    ssEq SSZero SSZero  = True
    ssEq SSZero _       = False
    ssEq _      SSZero  = False
    ssEq (SSNZ c d ~r) (SSNZ c' d' ~r')     = dCmp d d' == EQ && cEq c c' && ssEq r r'
    ssAG        = Group ssEq ssPlus SSZero ssIsZero ssNeg
    dc2ss d c   = ssLead' c d SSZero
    univF (Group _ vPlus vZero _ _) (TgtArrsF dc2v)   = go
      where
        go SSZero       = vZero
        go (SSNZ c d t) = vPlus !$ dc2v d c !$ go t

ssDotWith       :: Cmp d -> AbelianGroup c2 -> (c -> c1 -> c2) ->
    SparseSum c d -> SparseSum c1 d -> c2
ssDotWith dCmp c2AG f   = dot where
    dot s t     = if ssIsZero s || ssIsZero t then agZero c2AG else
        let d = ssDegNZ s
            e = ssDegNZ t
        in case d `dCmp` e of
            GT -> dot (ssTail s) t
            LT -> dot s (ssTail t)
            EQ -> agPlus c2AG !$ (f !$ ssHeadCoef s !$ ssHeadCoef t)
                    !$ dot (ssTail s) (ssTail t)

ssTimes         :: SparseSumUniv d c -> Op2 d -> Ring c -> Op2 (SparseSum c d)
-- ^ assumes the @Op2 d@ is order-preserving in each argument
ssTimes (UnivL ssAG _ univF) dOp2 (Ring cAG cTimes _ _ _) s t     =
    univF ssAG (TgtArrsF dcTimesT) s
  where
    dcTimesT d c    = ssShiftMapC (isZero cAG) (dOp2 d) (cTimes c) t


ssShowPrec      :: ShowPrec d -> ShowPrec c -> ShowPrec (SparseSum c d)
ssShowPrec dSP cSP prec x   =
    let s = ssFoldr (\ c d st -> plusS (timesS (cSP multPrec c) (dSP multPrec d)) st) "0" x
    in  if prec > addPrec && not (ssIsZero x) && not (ssIsZero (ssTail x)) || prec > multPrec
            then '(':s++")" else s
