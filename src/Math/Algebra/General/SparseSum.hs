{-# LANGUAGE Strict #-}

{- |  A 'SparseSum' is a linear combination where zero terms are omitted.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.General.SparseSum (
    SSTerm(..), SparseSum, pattern SSNZ, pattern SSZero, SparseSumUniv,
    ssIsZero, ssDegNZ, ssHeadCoef, ssTail, sparseSum, ssCons, ssUnconsNZ,
    ssLexCmp, ssDegCmp,
    ssLead, ssMapC, ssMapNZFC, ssShift, ssShiftMapC, ssShiftMapNZFC, ssFoldr, ssNumTerms,
    ssAGUniv, ssFoldSort, ssDotWith,
    ssNzdCTimes, ssCTimes, ssMonicizeU, ssTimesNzdC, ssTimesC, ssTimesNzdMonom, ssTimesMonom,
        ssTimesNzds, ssTimes,
    ssTermShowPrec, ssShowPrec, varPowShowPrec
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category

import Data.Foldable (toList)
import Data.List (sortBy)
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL


data SSTerm c d     = SSTerm { c :: c, d :: d }
    deriving (Eq, Show)     -- e.g. for testing & debugging

type SparseSum c d  = SL.List (SSTerm c d)
-- ^ a sorted list of non-\"zero\" terms, with \"degrees\" decreasing according to a total order

pattern SSNZ        :: c -> d -> SparseSum c d -> SparseSum c d
pattern SSNZ c d t  = SSTerm c d :! t
{-# INLINE SSNZ #-}

pattern SSZero      :: SparseSum c d
pattern SSZero      = SL.Nil
{-# INLINE SSZero #-}

{-# COMPLETE SSNZ, SSZero #-}

type SparseSumUniv d c ss   = UnivL AbelianGroup (TgtArrsF (->) c d) (->) ss
{- ^ an @AbelianGroup ss@, @dcToSS@ function, and a function for mapping to other
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
ssTail (_ :! t)         = t
ssTail SL.Nil           = undefined

sparseSum                       :: b -> (c -> d -> SparseSum c d -> b) -> SparseSum c d -> b
-- ^ like 'maybe' or 'either'
sparseSum ~z ~_ SSZero          = z
sparseSum ~_ ~f (SSNZ c d t)    = f c d t

ssCons                  :: SSTerm c d -> SparseSum c d -> SparseSum c d
ssCons                  = (:!)

ssUnconsNZ              :: SparseSum c d -> (SSTerm c d, SparseSum c d)
ssUnconsNZ (cd :! t)    = (cd, t)
ssUnconsNZ SL.Nil       = undefined

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

ssDegCmp        :: Cmp d -> IsDeep -> Cmp (SparseSum c d)
ssDegCmp dCmp deep s t
    | ssIsZero s        = if ssIsZero t then EQ else LT
    | ssIsZero t        = GT
    | otherwise         =
        let ord = dCmp (ssDegNZ s) (ssDegNZ t)
        in  if ord /= EQ || not deep.b then ord else ssDegCmp dCmp deep (ssTail s) (ssTail t)

ssLead          :: Pred c -> c -> d -> SparseSum c d -> SparseSum c d
-- ^ @ssLead cIs0 c d s@ assumes @d > degree(s)@
ssLead cIs0 c d t   = if cIs0 c then t else SSNZ c d t

ssMapC          :: Pred c' -> (c -> c') -> SparseSum c d -> SparseSum c' d
ssMapC is0 f    = go SSZero
  where
    go r (SSNZ c ~d t)  =
        let c'      = f c
        in  go (if is0 c' then r else SSTerm c' d :! r) t
    go r SSZero         = SL.reverse r

ssMapNZFC       :: (c -> c') -> SparseSum c d -> SparseSum c' d
-- ^ assumes the @(c -> c')@ takes nonzero values to nonzero values
ssMapNZFC f     = fmap (\cd@(SSTerm c _d) -> cd{ c = f c })

ssShift         :: (d -> d') -> SparseSum c d -> SparseSum c d'
-- ^ assumes the @(d -> d')@ is order-preserving
ssShift f       = fmap (\cd@(SSTerm _c d) -> cd{ d = f d })

ssShiftMapC     :: Pred c' -> (d -> d') -> (c -> c') -> SparseSum c d -> SparseSum c' d'
-- ^ assumes the @(d -> d')@ is order-preserving
ssShiftMapC is0 df cf   = go SSZero
  where
    go r (SSNZ c ~d t)      =
        let c'  = cf c
        in  go (if is0 c' then r else SSTerm c' (df d) :! r) t
    go r SSZero             = SL.reverse r

ssShiftMapNZFC  :: (d -> d') -> (c -> c') -> SparseSum c d -> SparseSum c' d'
{- ^ assumes the @(d -> d')@ is order-preserving, and the @(c -> c')@ takes nonzero values to
    nonzero values -}
ssShiftMapNZFC df cf    = fmap (\(SSTerm c d) -> SSTerm (cf c) (df d))

ssFoldr         :: (c -> d -> t -> t) -> t -> SparseSum c d -> t
ssFoldr f       = foldr (\(SSTerm c d) -> f c d)

ssNumTerms      :: SparseSum c d -> Int
ssNumTerms      = length

ssAGUniv        :: forall c d. AbelianGroup c -> Cmp d -> SparseSumUniv d c (SparseSum c d)
ssAGUniv (AbelianGroup _cFlags eq plus _zero isZero neg) dCmp   =
    UnivL ssAG (TgtArrsF dcToSS) univF
  where
    ssLead'     = ssLead isZero
    -- {-# SCC ssPlus #-}
    ssPlus      :: Op2 (SparseSum c d)
    ssPlus s@(t@(SSTerm ~c d) :! ~r) s'@(t'@(SSTerm ~c' d') :! ~r') =   -- {-# SCC ssPlusNZ #-}
        case d `dCmp` d' of
            GT  -> t  :! (r `ssPlus` s')
            LT  -> t' :! (s `ssPlus` r')
            EQ  -> ssLead' (c `plus` c') d (r `ssPlus` r')
    ssPlus s                         SL.Nil                         = s
    ssPlus SL.Nil                    t                              = t
    ssNeg       = ssMapNZFC neg
    ssEq        :: EqRel (SparseSum c d)
    ssEq SSZero SSZero  = True
    ssEq SSZero _       = False
    ssEq _      SSZero  = False
    ssEq (SSNZ c d ~r) (SSNZ c' d' ~r')     = dCmp d d' == EQ && eq c c' && ssEq r r'
    ssAG        = abelianGroup ssEq ssPlus SSZero ssIsZero ssNeg
    dcToSS d c  = ssLead' c d SSZero
    univF (AbelianGroup _ _ vPlus vZero _ _) (TgtArrsF dcToV)   = go
      where
        go SSZero       = vZero
        go (SSNZ c d t) = vPlus !$ dcToV d c !$ go t

ssFoldSort      :: AbelianGroup c -> Cmp d -> [SSTerm c d] -> SparseSum c d
-- ^ sorts and combines the terms; input terms may have coefs which are 0
ssFoldSort (AbelianGroup _ _ cPlus _ cIsZero _) dCmp cds0   =
    go SL.Nil (sortBy (dCmp `on` (.d)) cds0)
  where
    go done []          = done
    go done (cd : t)    = go1 done cd.d cd.c t
    go1 done d          = go2
      where
        go2 c (cd : t)
            | dCmp d cd.d == EQ     = go2 (cPlus c cd.c) t
        go2 c cds           = go (if cIsZero c then done else SSTerm c d :! done) cds

ssDotWith       :: Cmp d -> (c -> c1 -> c2) -> AbelianGroup c2 ->
                        SparseSum c d -> SparseSum c1 d -> c2
ssDotWith dCmp f (AbelianGroup { plus, zero })    = dot
  where
    dot s s'     = if ssIsZero s || ssIsZero s' then zero else
        let d = ssDegNZ s
            e = ssDegNZ s'
        in case d `dCmp` e of
            GT -> dot (ssTail s) s'
            LT -> dot s (ssTail s')
            EQ -> plus !$ (f !$ ssHeadCoef s !$ ssHeadCoef s') !$ dot (ssTail s) (ssTail s')

ssNzdCTimes     :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ the @c@ must not be a left zero divisor, i.e. @c*a = 0 => a = 0@
ssNzdCTimes (Ring { times }) c  = ssMapNZFC (c `times`)

ssCTimes        :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ If the @c@ is not a left zero divisor, then 'ssNzdCTimes' is faster.
ssCTimes cR@(Ring { times }) c  = ssMapC cR.isZero (c `times`)

ssMonicizeU     :: Ring c -> Op1 (SparseSum c d)
-- ^ @(ssMonicizeU s)@ requires that @s@ is nonzero, and its leading coefficient is a unit
ssMonicizeU cR@(Ring { times }) s   =
    let c       = ssHeadCoef s  -- check for c = 1 for speed
    in  if rIsOne cR c then s else ssMapNZFC (rInv cR c `times`) s

ssTimesNzdC     :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ the @c@ must not be a right zero divisor, i.e. @a*c = 0 => a = 0@
ssTimesNzdC (Ring { times }) c  = ssMapNZFC (`times` c)

ssTimesC        :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ If the @c@ is not a right zero divisor, then 'ssTimesNzdC' is faster.
ssTimesC cR@(Ring { times }) c  = ssMapC cR.isZero (`times` c)

ssTimesNzdMonom     :: Ring c -> Op2 d -> SparseSum c d -> d -> c -> SparseSum c d
-- ^ assumes the @Op2 d@ is order-preserving in each argument, and the @c@ is not a right zero
-- divisor
ssTimesNzdMonom (Ring { times }) dOp2 s d c     = ssShiftMapNZFC (`dOp2` d) (`times` c) s

ssTimesMonom    :: Ring c -> Op2 d -> SparseSum c d -> d -> c -> SparseSum c d
-- ^ assumes the @Op2 d@ is order-preserving in each argument. Also, if the @c@ is not a right
-- zero divisor, then 'ssTimesNzdMonom' is faster.
ssTimesMonom cR@(Ring { times }) dOp2 s d c     = ssShiftMapC cR.isZero (`dOp2` d) (`times` c) s

ssTimesNzds     :: SparseSumUniv d c (SparseSum c d) -> Ring c -> Op2 d -> Op2 (SparseSum c d)
-- ^ assumes the @Op2 d@ is order-preserving in each argument, and there are no nonzero right
-- zero divisors in @cR@
ssTimesNzds (UnivL ssAG _ univF) cR dOp2 s  = univF ssAG (TgtArrsF (sToTimesDC s))
  where
    sToTimesDC      = ssTimesNzdMonom cR dOp2

ssTimes         :: SparseSumUniv d c (SparseSum c d) -> Ring c -> Op2 d -> Op2 (SparseSum c d)
-- ^ assumes the @Op2 d@ is order-preserving in each argument. Also, if there are no nonzero
-- right zero divisors in @cR@, then 'ssTimesNzds' is faster.
ssTimes (UnivL ssAG _ univF) cR dOp2 s  = univF ssAG (TgtArrsF (sToTimesDC s))
  where
    sToTimesDC      = ssTimesMonom cR dOp2


ssTermShowPrec                  :: ShowPrec d -> ShowPrec c -> ShowPrec (SSTerm c d)
ssTermShowPrec dSP cSP prec cd  = timesSPrec cSP dSP prec cd.c cd.d

ssShowPrec              :: ShowPrec d -> ShowPrec c -> ShowPrec (SparseSum c d)
ssShowPrec dSP cSP prec = sumSPrec (ssTermShowPrec dSP cSP) prec . toList

varPowShowPrec          :: (Integral d, Show d) => String -> ShowPrec d
-- ^ varS prec > '^'
varPowShowPrec varS prec d  = case d of
    0   -> "1"
    1   -> varS
    _   -> parensIf (exptPrec < prec) (varS ++ '^' : show d)
