{-# LANGUAGE Strict #-}

{- |  A 'SparseSum' is a linear combination where zero terms are omitted.
    
    This module uses LANGUAGE Strict. In particular, constructor fields and function arguments
    are strict unless marked with a ~.
-}

module Math.Algebra.General.SparseSum (
    SSTerm(..), SparseSum, SparseSumUniv,
    ssZero, pattern (:!), sparseSum, ssHead,
    ssLexCmp, ssDegCmp,
    ssLead, ssMapC, ssMapNzFC, ssShift, ssShiftMapC, ssShiftMapNzFC,
    ssAGUniv, ssFoldSort, ssDotWith,
    ssNzdCTimes, ssCTimes, ssMonicizeU, ssTimesNzdC, ssTimesC, ssTimesNzdMonom, ssTimesMonom,
        ssTimesNzds, ssTimes,
    ssTermShowPrec, ssShowPrec
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category

import Data.Bifunctor (Bifunctor(first, second, bimap))
import Data.Foldable (toList)
import Data.Maybe (fromJust)
import GHC.Stack (HasCallStack)
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL


data SSTerm c d     = SSTerm { c :: c, d :: d }
    deriving (Eq, Show)     -- e.g. for testing & debugging

instance Functor (SSTerm c) where
    fmap f cd   = cd { d = f cd.d }
    {-# INLINE fmap #-}

instance Bifunctor SSTerm where
    bimap f g (SSTerm c d)  = SSTerm (f c) (g d)
    {-# INLINE bimap #-}
    first f cd              = cd { c = f cd.c }
    {-# INLINE first #-}
    second g cd             = cd { d = g cd.d }
    {-# INLINE second #-}

type SparseSum c d  = SL.List (SSTerm c d)
-- ^ a sorted list of non-\"zero\" terms, with \"degrees\" (or "basis elements") decreasing
-- according to a total order.

type SparseSumUniv d c ss   = UnivL AbelianGroup (TgtArrsF (->) c d) (->) ss
{- ^ an @AbelianGroup ss@, @dcToSS@ function, and a function for mapping to other
    t'AbelianGroup's @t@ that have a @d -> Hom_AG(c, t)@; \(⊕↙d C_d\) where each \(C_d\) is a
    copy of \(C\). -}


ssZero              :: SparseSum c d
ssZero              = SL.Nil

sparseSum           :: a -> (c -> d -> SparseSum c d -> a) -> SparseSum c d -> a
-- ^ like 'maybe' or 'either'
sparseSum ~z ~f x   = maybe z (\(SSTerm c d, t) -> f c d t) (SL.uncons x)
{-# INLINE sparseSum #-}

ssHead              :: HasCallStack => SparseSum c d -> SSTerm c d
ssHead x            = fst (fromJust (SL.uncons x))
{-# INLINE ssHead #-}

ssLexCmp        :: Cmp d -> c -> Cmp c -> Cmp (SparseSum c d)
-- ^ \"lexicographic\" comparison
ssLexCmp bCmp cZero cCmp        = ssCmp
  where
    ssCmp x y   = case SL.uncons x of
        Nothing                     -> case SL.uncons y of
            Nothing                     -> EQ
            Just (SSTerm !yc _, _)      -> cCmp cZero yc
        Just (SSTerm xc xd, xt)     -> case SL.uncons y of
            Nothing                     -> cCmp xc cZero
            Just (SSTerm yc !yd, yt)    -> case bCmp xd yd of
                GT  -> cCmp xc cZero
                LT  -> cCmp cZero yc
                EQ  -> cCmp xc yc <> ssCmp xt yt

ssDegCmp        :: Cmp d -> IsDeep -> Cmp (SparseSum c d)
ssDegCmp dCmp deep  = go
  where
    go x y  = case SL.uncons x of
        Nothing                 -> maybe EQ (const LT) (SL.uncons y)
        Just (SSTerm _ xd, xt)  -> case SL.uncons y of
            Nothing                 -> GT
            Just (SSTerm _ yd, yt)  ->
                let dOrd    = dCmp xd yd
                in  if dOrd /= EQ || not deep.b then dOrd else go xt yt

ssLead              :: Pred c -> c -> d -> SparseSum c d -> SparseSum c d
-- ^ @ssLead cIs0 c d s@ assumes @d > degree(s)@
ssLead cIs0 c ~d ~t = if cIs0 c then t else SSTerm c d :! t
{-# INLINE ssLead #-}

ssMapC          :: Pred c' -> (c -> c') -> SparseSum c d -> SparseSum c' d
-- ^ @ssMapC is0 f x@ applies @f@ to each coefficient in @x@.
ssMapC is0 f    = foldr k ssZero
  where
    k cd    = ssLead is0 (f cd.c) cd.d
{-# INLINABLE ssMapC #-}

ssMapNzFC       :: (c -> c') -> SparseSum c d -> SparseSum c' d
-- ^ assumes the @(c -> c')@ takes nonzero values to nonzero values
ssMapNzFC f     = fmap (first f)
{-# INLINE ssMapNzFC #-}

ssShift         :: (d -> d') -> SparseSum c d -> SparseSum c d'
-- ^ assumes the @(d -> d')@ is order-preserving
ssShift f       = fmap (second f)
{-# INLINE ssShift #-}

ssShiftMapC     :: Pred c' -> (d -> d') -> (c -> c') -> SparseSum c d -> SparseSum c' d'
-- ^ assumes the @(d -> d')@ is order-preserving
ssShiftMapC is0 df cf   = foldr k ssZero
  where
    k cd    = ssLead is0 (cf cd.c) (df cd.d)
{-# INLINABLE ssShiftMapC #-}

ssShiftMapNzFC  :: (d -> d') -> (c -> c') -> SparseSum c d -> SparseSum c' d'
{- ^ assumes the @(d -> d')@ is order-preserving, and the @(c -> c')@ takes nonzero values to
    nonzero values -}
ssShiftMapNzFC df cf    = fmap (bimap cf df)
{-# INLINE ssShiftMapNzFC #-}

ssAGUniv        :: AbelianGroup c -> Cmp d -> SparseSumUniv d c (SparseSum c d)
-- ^ The result's @monFlags@ assumes @(d)@ is nonempty.
ssAGUniv (AbelianGroup cFlags eq plus _zero isZero neg) dCmp    =
    UnivL ssAG (TgtArrsF dcToSS) univF
  where
    ssLead'     = ssLead isZero
    ssPlus x y  = case SL.uncons x of
        Nothing                         -> y
        Just (xh@(SSTerm xc xd), xt)    -> case SL.uncons y of
            Nothing                         -> x
            Just (yh@(SSTerm yc !yd), yt)   -> case xd `dCmp` yd of
                GT  -> xh :! xt `ssPlus` y
                LT  -> yh :! x `ssPlus` yt
                EQ  -> ssLead' (xc `plus` yc) yd (xt `ssPlus` yt)
    ssNeg       = ssMapNzFC neg
    ssEq x y    = case SL.uncons x of
        Nothing                     -> null y
        Just (SSTerm xc xd, xt)     -> case SL.uncons y of
            Nothing                     -> False
            Just (SSTerm yc yd, yt)     -> dCmp xd yd == EQ && eq xc yc && ssEq xt yt
    ssFlags     = agFlags (IsNontrivial cFlags.nontrivial)
    ssAG        = AbelianGroup ssFlags ssEq ssPlus ssZero null ssNeg
    dcToSS d c  = ssLead' c d ssZero
    univF (AbelianGroup _ _ vPlus vZero _ _) (TgtArrsF dcToV)   = go
      where
        go  = sparseSum vZero (\c d t -> vPlus !$ dcToV d c !$ go t)

ssFoldSort      :: AbelianGroup c -> Cmp d -> [SSTerm c d] -> SparseSum c d
-- ^ sorts and combines the terms; input terms may have coefs which are 0
ssFoldSort (AbelianGroup _ _ cPlus _ cIsZero _) dCmp cds0   =
    go ssZero (sortLBy (dCmp `on` (.d)) cds0)
  where
    go done []          = done
    go done (cd : t)    = go1 done cd.d cd.c t
    go1 done d          = go2
      where
        go2 c (cd : t)
            | dCmp d cd.d == EQ     = go2 (cPlus c cd.c) t
        go2 c cds           = go (if cIsZero c then done else SSTerm c d :! done) cds

ssDotWith       :: AbelianGroup c2 -> Cmp d -> (c -> c1 -> c2) ->
                        SparseSum c d -> SparseSum c1 d -> c2
ssDotWith (AbelianGroup { plus, zero }) dCmp f  = dot
  where
    dot x y         = maybe zero xGo (SL.uncons x)
      where
        xGo (SSTerm xc !xd, xt)     = maybe zero yGo (SL.uncons y)
          where
            yGo (SSTerm yc !yd, yt)     = case xd `dCmp` yd of
                GT  -> dot xt y
                LT  -> dot x yt
                EQ  -> plus !$ (f !$ xc !$ yc) !$ dot xt yt

ssNzdCTimes     :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ the @c@ must not be a left zero divisor, i.e. @c*a = 0 => a = 0@
ssNzdCTimes (Ring { times }) c  = ssMapNzFC (c `times`)

ssCTimes        :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ If the @c@ is not a left zero divisor, then 'ssNzdCTimes' is faster.
ssCTimes cR@(Ring { times }) c  = ssMapC cR.isZero (c `times`)

ssMonicizeU     :: Ring c -> Op1 (SparseSum c d)
-- ^ @(ssMonicizeU s)@ requires that @s@ is nonzero, and its leading coefficient is a unit
ssMonicizeU cR@(Ring { times }) s   =
    let c       = (ssHead s).c  -- check for c = 1 for speed
    in  if rIsOne cR c then s else ssMapNzFC (rInv cR c `times`) s

ssTimesNzdC     :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ the @c@ must not be a right zero divisor, i.e. @a*c = 0 => a = 0@
ssTimesNzdC (Ring { times }) c  = ssMapNzFC (`times` c)

ssTimesC        :: Ring c -> c -> Op1 (SparseSum c d)
-- ^ If the @c@ is not a right zero divisor, then 'ssTimesNzdC' is faster.
ssTimesC cR@(Ring { times }) c  = ssMapC cR.isZero (`times` c)

ssTimesNzdMonom     :: Ring c -> Op2 d -> SparseSum c d -> d -> c -> SparseSum c d
-- ^ assumes the @Op2 d@ is order-preserving in each argument, and the @c@ is not a right zero
-- divisor
ssTimesNzdMonom (Ring { times }) dOp2 s d c     = ssShiftMapNzFC (`dOp2` d) (`times` c) s

ssTimesMonom    :: Ring c -> Op2 d -> SparseSum c d -> d -> c -> SparseSum c d
-- ^ assumes the @Op2 d@ is order-preserving in each argument. Also, if the @c@ is not a right
-- zero divisor, then 'ssTimesNzdMonom' is faster.
ssTimesMonom cR@(Ring { times }) dOp2 s d c     = ssShiftMapC cR.isZero (`dOp2` d) (`times` c) s

ssTimesNzds     :: SparseSumUniv d c (SparseSum c d) -> Ring c -> Op2 d ->
                    Op2 (SparseSum c d)
-- ^ assumes the @Op2 d@ is order-preserving in each argument, and there are no nonzero right
-- zero divisors in @cR@
ssTimesNzds (UnivL ssAG _ univF) cR dOp2 s  = univF ssAG (TgtArrsF (sToTimesDC s))
  where
    sToTimesDC      = ssTimesNzdMonom cR dOp2

ssTimes         :: SparseSumUniv d c (SparseSum c d) -> Ring c -> Op2 d ->
                    Op2 (SparseSum c d)
-- ^ assumes the @Op2 d@ is order-preserving in each argument. Also, if there are no nonzero
-- right zero divisors in @cR@, then 'ssTimesNzds' is faster.
ssTimes (UnivL ssAG _ univF) cR dOp2 s  = univF ssAG (TgtArrsF (sToTimesDC s))
  where
    sToTimesDC      = ssTimesMonom cR dOp2


ssTermShowPrec  :: ShowPrec d -> ShowPrec c -> ShowPrec (SSTerm c d)
ssTermShowPrec dSP cSP cd   = timesPT (cSP cd.c) (dSP cd.d)

ssShowPrec      :: ShowPrec d -> ShowPrec c -> ShowPrec (SparseSum c d)
ssShowPrec dSP cSP  = sumPT . map (ssTermShowPrec dSP cSP) . toList
