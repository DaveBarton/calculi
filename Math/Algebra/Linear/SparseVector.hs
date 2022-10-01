{-# LANGUAGE Strict #-}

{- |  A 'SparseVector' is a finite sequence of coordinates (basis coefficients), implemented as
    a strict IntMap where zeros are omitted.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Linear.SparseVector (
    -- * SparseVector
    SparseVector(..), SparseVectorUniv,
    svZero, pICToSV, svIsZero, svSize, svMapC, svMapNZFC, svFoldr',
    svAGUniv, svDotWith, svNZCTimes, svCTimes, svMonicize, svTimesNZC, svTimesC, svSwap,
    svShowPrec,
    
    -- * SparseMatrix
    SparseColsMat, scmPDiag, scmCol, scmTimesV, scmRing, scmTranspose
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Maybe (isNothing)


-- * SparseVector

newtype SparseVector c  = SV { unSV :: IntMap c }
    deriving (Eq, Show)     -- Eq & Show e.g. for testing & debugging
{- ^ a finite sequence of coordinates (basis coefficients), indexed starting at 0. Coordinates
    which are zero must be omitted. -}

type SparseVectorUniv c     = UnivL AbelianGroup (TgtArrsF (->) c Int) (->) (SparseVector c)
{- ^ an @AbelianGroup (SparseVector c)@, @iCToSV@ function, and a function for mapping to
    other 'AbelianGroup's @t@ that have an @Int -> Hom_AG(c, t)@; \(⊕↙i C_i\) where each \(C_i\)
    is a copy of \(C\). -}


svZero          :: SparseVector c
svZero          = SV IM.empty

pICToSV         :: Pred c -> Int -> c -> SparseVector c
pICToSV cIsZero i c     = if cIsZero c then svZero else SV (IM.singleton i c)

svIsZero        :: SparseVector c -> Bool
svIsZero        = IM.null . unSV

svSize          :: (SparseVector c) -> Int
-- ^ \(n\), the number of nonzero coefficients; \(O(n)\)
svSize          = IM.size . unSV

svMapC          :: Pred c' -> (c -> c') -> SparseVector c -> SparseVector c'
svMapC is0 f (SV m)     = SV (IM.filter (not . is0) (IM.map f m))

svMapNZFC       :: (c -> c') -> SparseVector c -> SparseVector c'
-- ^ assumes the @(c -> c')@ takes nonzero values to nonzero values
svMapNZFC f (SV m)  = SV (IM.map f m)

svFoldr'        :: (Op2 t) -> t -> (Int -> c -> t) -> SparseVector c -> t
svFoldr' tPlus tZero iCToT (SV m)   = IM.foldrWithKey' (\i c -> tPlus $! iCToT i c) tZero m

svAGUniv        :: forall c. IAbelianGroup c => SparseVectorUniv c
svAGUniv        = UnivL svAG (TgtArrsF iCToSV) univF
  where
    maybePlus       :: Int -> c -> c -> Maybe c
    maybePlus _ a b     = let c = a +. b in if isZero c then Nothing else Just c
    svPlus (SV m) (SV m')   = SV (IM.mergeWithKey maybePlus id id m m')
    svNeg (SV m)    = SV (IM.map (neg @c) m)
    svEq            = liftEq ((==.) @c) `on` unSV
    svAG            = Group agFlags svEq svPlus svZero svIsZero svNeg
    iCToSV          = pICToSV (isZero @c)
    univF (Group _ _ tPlus tZero _ _) (TgtArrsF iCToT)  = svFoldr' tPlus tZero iCToT

svDotWith       :: IAbelianGroup c2 => (c -> c1 -> c2) ->
                    SparseVector c -> SparseVector c1 -> c2
svDotWith f (SV m) (SV m')   = IM.foldr' (+.) zero (IM.intersectionWith f m m')

svNZCTimes      :: forall c. IRing c => c -> Op1 (SparseVector c)
-- ^ the @c@ is nonzero
svNZCTimes
    | hasEIBit (iRFlags @c) NoZeroDivisors  = \c -> svMapNZFC (c *.)
    | otherwise                             = \c -> svMapC isZero (c *.)

svCTimes        :: IRing c => c -> Op1 (SparseVector c)
svCTimes c v    = if isZero c then svZero else svNZCTimes c v

svMonicize      :: IRing c => Int -> Op1 (SparseVector c)
-- ^ @(svMonicize i v)@ requires that the @i@'th coefficient of @v@ is a unit
svMonicize i (SV m)     = SV (IM.map ((rInv (m IM.! i)) *.) m)

svTimesNZC      :: forall c. IRing c => c -> Op1 (SparseVector c)
-- ^ the @c@ is nonzero
svTimesNZC
    | hasEIBit (iRFlags @c) NoZeroDivisors  = \c -> svMapNZFC (*. c)
    | otherwise                             = \c -> svMapC isZero (*. c)

svTimesC        :: IRing c => c -> Op1 (SparseVector c)
svTimesC c v    = if isZero c then svZero else svTimesNZC c v

svSwap          :: Int -> Int -> Op1 (SparseVector c)
-- ^ swaps two coefficients
svSwap i j v@(SV m)     =
    let mc  = m IM.!? i
        md  = m IM.!? j
    in  if isNothing mc && isNothing md then v  -- for efficiency
        else SV (IM.alter (const mc) j (IM.alter (const md) i m))


svShowPrec      :: ShowPrec Int -> ShowPrec c -> ShowPrec (SparseVector c)
svShowPrec iSP cSP prec v@(SV m)  =
    let s   = svFoldr' plusS "0" (\i c -> timesS (cSP multPrec c) (iSP multPrec i)) v
    in  if prec > multPrec || prec > addPrec && length (IM.splitRoot m) > 1
        then '(':s++")" else s


-- * SparseMatrix

type SparseColsMat c    = SparseVector (SparseVector c)
{- ^ a matrix stored as columns, implementing a linear map between finitely generated right
    R-modules with basis elements indexed starting at 0. The columns are the images of the
    source module's basis elements. -}

scmPDiag        :: Pred c -> Int -> c -> SparseColsMat c
scmPDiag cIsZero n c    = if cIsZero c then svZero else
    SV (IM.fromDistinctAscList [(i, SV (IM.singleton i c)) | i <- [0 .. n - 1]])

scmCol          :: SparseColsMat c -> Int -> SparseVector c
scmCol mat j    = IM.findWithDefault svZero j (unSV mat)

scmTimesV       :: (IRing c, IAbelianGroup (SparseVector c)) =>
                    SparseColsMat c -> Op1 (SparseVector c)
scmTimesV       = svDotWith (flip svTimesNZC)

scmRing         :: forall c. IRing c => Int -> Ring (SparseColsMat c)
-- ^ ring of matrices. @one@ and @fromZ@ of @scmRing n@ will create @n x n@ matrices.
scmRing maxN    = Ring ag matFlags (*~) one' fromZ' bDiv2'
  where
    UnivL vAG (TgtArrsF _iCToV) _vUnivF = svAGUniv @c
    UnivL ag (TgtArrsF _jVToMat) _vvUnivF   = withAG vAG svAGUniv
    matFlags        = case maxN of
        0   -> eiBits [IsCommutativeRing, NoZeroDivisors, IsInversesRing]
        1   -> iRFlags @c
        _   -> eiBit NotZeroRing .&. (iRFlags @c)
    a *~ b          = svMapC svIsZero (withAG vAG scmTimesV a) b
    one'            = scmPDiag isZero maxN one
    fromZ' z        = scmPDiag isZero maxN (fromZ z)
    bDiv2' _doFull y _t     = (svZero, y)   -- @@ improve (incl. solving linear equations in parallel)

scmTranspose    :: Op1 (SparseColsMat c)
scmTranspose (SV cols)  = SV $ case IM.splitRoot cols of
    []      -> IM.empty
    [_]     -> IM.foldrWithKey' (\j v t -> IM.union (IM.map (SV . (IM.singleton j)) (unSV v)) t)
                    IM.empty cols
    colss   -> IM.unionsWith (SV .* (IM.union `on` unSV)) (map (unSV . scmTranspose . SV) colss)
