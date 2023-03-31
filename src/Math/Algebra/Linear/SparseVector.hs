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
    svAGUniv, svDotWith, SVOverRingOps(..), svOverRingOps, svSwap,
    svShowPrec,
    
    -- * SparseMatrix
    SparseColsMat, scmPDiag, scmCol, SCMOps(..), scmOps, scmTranspose
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum (SparseSumUniv)

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Maybe (isNothing)


-- * SparseVector

newtype SparseVector c  = SV { im :: IntMap c }
    deriving (Eq, Show)     -- Eq & Show e.g. for testing & debugging
{- ^ a finite sequence of coordinates (basis coefficients), indexed starting at 0. Coordinates
    which are zero must be omitted. -}

type SparseVectorUniv c     = SparseSumUniv Int c (SparseVector c)
{- ^ an @AbelianGroup (SparseVector c)@, @iCToSV@ function, and a function for mapping to
    other 'AbelianGroup's @t@ that have an @Int -> Hom_AG(c, t)@; \(⊕↙i C_i\) where each \(C_i\)
    is a copy of \(C\). -}


svZero          :: SparseVector c
svZero          = SV IM.empty

pICToSV         :: Pred c -> Int -> c -> SparseVector c
pICToSV cIsZero i c     = if cIsZero c then svZero else SV (IM.singleton i c)

svIsZero        :: SparseVector c -> Bool
svIsZero        = IM.null . (.im)

svSize          :: SparseVector c -> Int
-- ^ \(n\), the number of nonzero coefficients; \(O(n)\)
svSize          = IM.size . (.im)

svMapC          :: Pred c' -> (c -> c') -> SparseVector c -> SparseVector c'
svMapC is0 f (SV m)     = SV (IM.filter (not . is0) (IM.map f m))

svMapNZFC       :: (c -> c') -> SparseVector c -> SparseVector c'
-- ^ assumes the @(c -> c')@ takes nonzero values to nonzero values
svMapNZFC f (SV m)  = SV (IM.map f m)

svFoldr'        :: Op2 t -> t -> (Int -> c -> t) -> SparseVector c -> t
svFoldr' tPlus tZero iCToT (SV m)   = IM.foldrWithKey' (\i c -> tPlus $! iCToT i c) tZero m

svAGUniv        :: forall c. AbelianGroup c -> SparseVectorUniv c
svAGUniv (AbelianGroup _cFlags eq plus _zero isZero neg)    = UnivL svAG (TgtArrsF iCToSV) univF
  where
    maybePlus       :: Int -> c -> c -> Maybe c
    maybePlus _ a b     = let c = a `plus` b in if isZero c then Nothing else Just c
    svPlus (SV m) (SV m')   = SV (IM.mergeWithKey maybePlus id id m m')
    svNeg (SV m)    = SV (IM.map neg m)
    svEq            = liftEq eq `on` (.im)
    svAG            = abelianGroup svEq svPlus svZero svIsZero svNeg
    iCToSV          = pICToSV isZero
    univF (AbelianGroup _ _ tPlus tZero _ _) (TgtArrsF iCToT)   = svFoldr' tPlus tZero iCToT

svDotWith       :: (c -> c1 -> c2) -> AbelianGroup c2 -> SparseVector c -> SparseVector c1 -> c2
svDotWith f (AbelianGroup _ _ plus zero _ _) (SV m) (SV m')     =
    IM.foldr' plus zero (IM.intersectionWith f m m')

data SVOverRingOps c    = SVOverRingOps {
    nzcTimes        :: c -> Op1 (SparseVector c),   -- ^ the @c@ is nonzero
    cTimes          :: c -> Op1 (SparseVector c),
    monicize        :: Int -> Op1 (SparseVector c),
        -- ^ @(monicize i v)@ requires that the @i@'th coefficient of @v@ is a unit
    timesNZC        :: c -> Op1 (SparseVector c),   -- ^ the @c@ is nonzero
    timesC          :: c -> Op1 (SparseVector c)
}
svOverRingOps                   :: forall c. Ring c -> SVOverRingOps c
svOverRingOps cR@(Ring { .. })  = SVOverRingOps { .. }
  where
    isZero      = ag.isIdent
    nzcTimes
        | hasEIBit rFlags NoZeroDivisors    = \c -> svMapNZFC (c `times`)
        | otherwise                         = \c -> svMapC isZero (c `times`)
    cTimes c v  = if isZero c then svZero else nzcTimes c v
    monicize i v@(SV m)     =
        let c       = m IM.! i  -- check for c = 1 for speed
        in  if rIsOne cR c then v else svMapNZFC (rInv cR c `times`) v
    timesNZC
        | hasEIBit rFlags NoZeroDivisors    = \c -> svMapNZFC (`times` c)
        | otherwise                         = \c -> svMapC isZero (`times` c)
    timesC c v    = if isZero c then svZero else timesNZC c v

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
scmCol mat j    = IM.findWithDefault svZero j mat.im

data SCMOps c   = SCMOps {
    vModR           :: ModR c (SparseVector c),
    scmTimesV       :: SparseColsMat c -> Op1 (SparseVector c),
    scmRing         :: Ring (SparseColsMat c)
}
scmOps          :: forall c. Ring c -> Int -> SCMOps c
-- ^ ring of matrices. @one@ and @fromZ@ of @scmOps cR n@ will create @n x n@ matrices.
scmOps cR maxN  = SCMOps { .. }
  where
    cIsZero         = rIsZero cR
    UnivL vAG (TgtArrsF _iCToV) _vUnivF     = svAGUniv cR.ag
    vOverCRingA     = svOverRingOps cR
    vModR           = Module vAG vOverCRingA.timesC
    UnivL ag (TgtArrsF _jVToMat) _vvUnivF   = svAGUniv vAG
    scmTimesV       = svDotWith (flip vOverCRingA.timesNZC) vAG
    matFlags        = case maxN of
        0   -> eiBits [IsCommutativeRing, NoZeroDivisors, IsInversesRing]
        1   -> cR.rFlags
        _   -> eiBit NotZeroRing .&. cR.rFlags
    a *~ b          = svMapC svIsZero (scmTimesV a) b
    one             = scmPDiag cIsZero maxN cR.one
    fromZ z         = scmPDiag cIsZero maxN (cR.fromZ z)
    scmRing         = Ring ag matFlags (*~) one fromZ bDiv
    bDiv _doFull y _t       = (svZero, y)   -- @@ improve (incl. solving linear equations in parallel)

scmTranspose    :: Op1 (SparseColsMat c)
scmTranspose (SV cols)  = SV $ case IM.splitRoot cols of
    []      -> IM.empty
    [_]     -> IM.foldrWithKey' (\j v t -> IM.union (IM.map (SV . IM.singleton j) v.im) t)
                    IM.empty cols
    colss   -> IM.unionsWith (SV .* (IM.union `on` (.im)))
                (map ((.im) . scmTranspose . SV) colss)
