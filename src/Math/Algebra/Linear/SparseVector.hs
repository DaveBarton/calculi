{-# LANGUAGE Strict #-}

{- |  A 'SparseVector' is a finite sequence of coordinates (basis coefficients), implemented as
    a strict IntMap where zeros are omitted.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Linear.SparseVector (
    -- * SparseVector
    SparseVector(..), SparseVectorUniv,
    svZero, pICToSV, svReplaceC, svIsZero, svCoord, svSize, svMapC, svMapNZFC, svFoldr',
    svAGUniv, svDotWith, svTimesNzdC, svTimesC, svMonicizeU, svSwap,
    svShowPrec,
    
    -- * SparseMatrix
    SparseColsMat, scmPDiag, scmCol, SCMOps(..), scmOps, scmTranspose
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum (SparseSumUniv)

import Control.Monad.Extra (pureIf)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Maybe (fromMaybe, isNothing)


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

svReplaceC              :: Pred c -> Int -> c -> Op1 (SparseVector c)
svReplaceC cIsZero i c  = SV . (if cIsZero c then IM.delete i else IM.insert i c) . (.im)

svIsZero        :: SparseVector c -> Bool
svIsZero        = IM.null . (.im)

svCoord             :: c -> Int -> SparseVector c -> c
svCoord cZero i v   = fromMaybe cZero (v.im IM.!? i)

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
    univF tAG (TgtArrsF iCToT)  = svFoldr' tAG.plus tAG.zero iCToT

svDotWith       :: (c -> c1 -> c2) -> AbelianGroup c2 -> SparseVector c -> SparseVector c1 -> c2
svDotWith f (AbelianGroup { plus, zero }) (SV m) (SV m')    =
    IM.foldr' plus zero (IM.intersectionWith f m m')

svTimesNzdC     :: Ring c -> c -> Op1 (SparseVector c)
-- ^ the @c@ must not be a right zero divisor, i.e. @a*c = 0 => a = 0@
svTimesNzdC (Ring { times }) c  = svMapNZFC (`times` c)

svTimesC        :: Ring c -> c -> Op1 (SparseVector c)
-- ^ If the @c@ is not a right zero divisor, then 'svTimesNzdC' is faster.
svTimesC cR@(Ring { times }) c  = svMapC cR.isZero (`times` c)

svMonicizeU     :: Ring c -> Int -> Op1 (SparseVector c)
-- ^ @(svMonicizeU cR i v)@ requires that the @i@'th coefficient of @v@ is a unit (and nonzero)
svMonicizeU cR@(Ring { times }) i v@(SV m)  =
    let c       = m IM.! i  -- check for c = 1 for speed
    in  if rIsOne cR c then v else svMapNZFC (`times` rInv cR c) v

svSwap          :: Int -> Int -> Op1 (SparseVector c)
-- ^ swaps two coefficients
svSwap i j v@(SV m)     =
    let mc  = m IM.!? i
        md  = m IM.!? j
    in  if isNothing mc && isNothing md then v  -- for efficiency
        else SV (IM.alter (const mc) j (IM.alter (const md) i m))


svShowPrec      :: ShowPrec Int -> ShowPrec c -> ShowPrec (SparseVector c)
svShowPrec iSP cSP prec v   = sumSPrec termSP prec (IM.toList v.im)
  where
    termSP prec1 (i, c) = timesSPrec cSP iSP prec1 c i


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

data PLUQ c     = PLUQ { pi, p, l, u, q, qi :: SparseColsMat c, r :: Int }
-- ^ A matrix factorization @p * l * u * q@ where:
--  * @p@ and @q@ are permutation matrices
--  * @pi@ and @qi@ are the inverses of @p@ and @q@
--  * @l@ and @u@ are /lower/ and /upper trapezoidal/ respectively
--      (@i \< j => l[i, j] = u[j, i] = 0@)
--  * @0 \<= i \< r => l[i, i]@ and @u[i, i]@ are units
--  * @r \<= i => l[j, i] = u[i, j] = 0@
--
-- Descriptively, @l@ has @r@ columns and @u@ has @r@ rows, their main diagonal elements are
-- units, and they are 0 before that.

data SCMOps c   = SCMOps {
    vModR           :: ModR c (SparseVector c),
    scmTimesV       :: SparseColsMat c -> Op1 (SparseVector c),
    scmRing         :: Ring (SparseColsMat c),
    upperTriSolve   :: SparseColsMat c -> Op1 (SparseVector c),
        -- ^ @upperTriSolve m v@ returns the unique @w@ such that @m * w = v@. @m@ must be upper
        -- triangular, and its main diagonal elements must be units starting when @v@ becomes
        -- nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then @m[k, k]@ must be a unit.
    lowerTrDivBy    :: SparseColsMat c -> SparseVector c -> (SparseVector c, SparseVector c),
        -- ^ @lowerTrDivBy m v = (q, r) => v = m*q + r@ and @rows[0 .. t](r) = 0@; where @m@
        -- is lower trapezoidal, has max column @t@, and its main diagonal elements are units
        -- starting when @v@ becomes nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then
        -- @m[k, k]@ must be a unit.
    lowerTriSolve   :: SparseColsMat c -> Op1 (SparseVector c)
        -- ^ @lowerTriSolve m v@ returns the unique @w@ such that @m * w = v@. @m@ must be lower
        -- triangular, and its main diagonal elements must be units starting when @v@ becomes
        -- nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then @m[k, k]@ must be a unit.
}
scmOps          :: forall c. Ring c -> Int -> SCMOps c
-- ^ ring of matrices. @one@ and @fromZ@ of @scmOps cR n@ will create @n x n@ matrices.
scmOps cR maxN  = SCMOps { .. }
  where
    cIsZero         = cR.isZero
    UnivL vAG (TgtArrsF _iCToV) _vUnivF     = svAGUniv cR.ag
    cNzds           = hasEIBit cR.rFlags NoZeroDivisors
    timesNzC        = (if cNzds then svTimesNzdC else svTimesC) cR
    timesNzdsC c v  = if cIsZero c then svZero else svTimesNzdC cR c v
    vBDiv doFull v@(SV vm) (SV wm)  = fromMaybe (cR.zero, v) $ do
        (i, wc)     <- IM.lookupMin wm
        vc          <- if doFull.b then vm IM.!? i else
                        do (vi, c) <- IM.lookupMin vm; pureIf (vi == i) c
        let (q, cr) = cR.bDiv doFull vc wc
        pureIf (not (cIsZero q))    -- for speed
            (q, vAG.plus (svReplaceC cIsZero i cr v)
                         (timesNzC (cR.neg q) (SV (IM.delete i wm))))
    vModR           = Module vAG (if cNzds then timesNzdsC else svTimesC cR) vBDiv
    UnivL ag (TgtArrsF _jVToMat) _vvUnivF   = svAGUniv vAG
    scmTimesV       = flip (svDotWith timesNzC vAG)
    matFlags        = case maxN of
        0   -> eiBits [IsCommutativeRing, NoZeroDivisors, IsInversesRing]
        1   -> cR.rFlags
        _   -> eiBit NotZeroRing .&. cR.rFlags
    a *~ b          = svMapC svIsZero (scmTimesV a) b
    one             = scmPDiag cIsZero maxN cR.one
    fromZ z         = scmPDiag cIsZero maxN (cR.fromZ z)
    scmRing         = Ring ag matFlags (*~) one fromZ bDiv
    upperTriSolve m     = loop []
      where
        loop done v     = case IM.maxViewWithKey v.im of
            Nothing                 -> SV (IM.fromDistinctAscList done)
            Just ((!i, !c), !v1)    -> loop ((i, r) : done) v2
              where     -- want m * w2 = v2 => m * ((i, r), w2) = ((i, c), v1)
                ((j, d), col1)  = IM.deleteFindMax (m.im IM.! i).im
                r   = assert (j == i) $ exactQuo cR c d
                v2  = vAG.plus (SV v1) (timesNzC (cR.neg r) (SV col1))
    lowerTrDivBy m      = loop []
      where
        t   = maybe 0 fst (IM.lookupMax m.im)
        loop done v     = case IM.minViewWithKey v.im of
            Nothing             -> end
            Just ((i, c), v1)   -> if i > t then end else
                let     -- want m * w2 + r = v2 => m * ((i, q), w2) + r = ((i, c), v1)
                    ((j, d), col1)  = IM.deleteFindMin (m.im IM.! i).im
                    q   = assert (j == i) $ exactQuo cR c d
                    v2  = vAG.plus (SV v1) (timesNzC (cR.neg q) (SV col1))
                in  loop ((i, q) : done) v2
          where
            ~end    = (SV (IM.fromDistinctAscList (reverse done)), v)
    lowerTriSolve m v   = assert (svIsZero r) q
      where
        (q, r)  = lowerTrDivBy m v
    bDiv _doFull y _t       = (svZero, y)   -- @@ improve (incl. solving linear equations in parallel)

scmTranspose    :: Op1 (SparseColsMat c)
scmTranspose (SV cols)  = SV $ case IM.splitRoot cols of
    []      -> IM.empty
    [_]     -> IM.foldrWithKey' (\j v t -> IM.union (IM.map (SV . IM.singleton j) v.im) t)
                    IM.empty cols
    colss   -> IM.unionsWith (SV .* (IM.union `on` (.im)))
                (map ((.im) . scmTranspose . SV) colss)
