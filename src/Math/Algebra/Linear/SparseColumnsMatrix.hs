{-# LANGUAGE Strict #-}

{- |  A sparse columns 'Matrix' is implemented as a 'SV.Vector' of 'SV.Vector's.
    
    This data structure is also fairly efficient for dense matrices.
    
    This module uses LANGUAGE Strict. In particular, constructor fields and function arguments
    are strict unless marked with a ~. Also, a 'Matrix' is strict in both its spine and its
    elements. Finally, "Data.Strict.Maybe" and "Data.Strict.Tuple" may be often used.
-}

module Math.Algebra.Linear.SparseColumnsMatrix (
    -- * Matrix
    Matrix,
    -- * Inlinable function(s)
    getCol,
    -- * Other functions
    PLUQMats(..), MatrixOps(..), matrixOps, transpose
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Linear.SparseVector as SV

import Control.Monad.Extra (pureIf)
import Data.Maybe (fromMaybe)
import Data.Strict.Classes (toLazy)
import qualified Data.Strict.Maybe as S
import qualified Data.Strict.Tuple as S
import Data.Strict.Tuple ((:!:), pattern (:!:))


-- * Matrix

type Matrix c   = SV.Vector (SV.Vector c)
{- ^ a matrix stored as columns, implementing a linear map between finitely generated right
    R-modules with basis elements indexed starting at 0. The columns are the images of the
    source module's basis elements. -}

-- * Inlinable function(s)

getCol          :: Matrix c -> Int -> SV.Vector c
getCol          = SV.index SV.zero

-- * Other functions

data PLUQMats c     = PLUQMats { pi, p, l, u, q, qi :: Matrix c, r :: Int }
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

data MatrixOps c   = MatrixOps {
    vModR           :: ModR c (SV.Vector c),
    matTimesV       :: Matrix c -> Op1 (SV.Vector c),
    matRing         :: Ring (Matrix c),
    diagNMat        :: Int -> c -> Matrix c,    -- ^ create a diagonal nxn matrix
    upperTriSolve   :: Matrix c -> Op1 (SV.Vector c),
        -- ^ @upperTriSolve m v@ returns the unique @w@ such that @m * w = v@. @m@ must be upper
        -- triangular, and its main diagonal elements must be units starting when @v@ becomes
        -- nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then @m[k, k]@ must be a unit.
    lowerTrDivBy    :: Matrix c -> SV.Vector c -> (SV.Vector c, SV.Vector c),
        -- ^ @lowerTrDivBy m v = (q, r) => v = m*q + r@ and @rows[0 .. t](r) = 0@; where @m@
        -- is lower trapezoidal, has max column @t@, and its main diagonal elements are units
        -- starting when @v@ becomes nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then
        -- @m[k, k]@ must be a unit.
    lowerTriSolve   :: Matrix c -> Op1 (SV.Vector c)
        -- ^ @lowerTriSolve m v@ returns the unique @w@ such that @m * w = v@. @m@ must be lower
        -- triangular, and its main diagonal elements must be units starting when @v@ becomes
        -- nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then @m[k, k]@ must be a unit.
}
matrixOps       :: forall c. Ring c -> Int -> MatrixOps c
{- ^ ring of matrices. @one@ and @fromZ@ of @matrixOps cR n@ will create @n x n@ matrices.
    @matRing.ag.monFlags.nontrivial@ assumes @n > 0@. -}
matrixOps cR maxN   = MatrixOps { .. }
  where
    cIsZero         = cR.isZero
    vAG             = SV.mkAG cR.ag
    cFlags          = cR.rFlags
    cNzds           = cFlags.noZeroDivisors
    timesNzC        = (if cNzds then SV.timesNzdC else SV.timesC) cR
    timesNzdsC c v  = if cIsZero c then SV.zero else SV.timesNzdC cR c v
    minusTimesNzC v q w     = vAG.plus v $! timesNzC (cR.neg q) w
    vBDiv doFull v w    = fromMaybe (cR.zero, v) $ do
        i :!: wc    <- toLazy $ SV.headPairMaybe w
        vc          <- if doFull.b then toLazy $ SV.indexMaybe v i else
                        do vi :!: c <- toLazy $ SV.headPairMaybe v; pureIf (vi == i) c
        let (q, _)  = cR.bDiv doFull vc wc
        pureIf (not (cIsZero q)) (q, minusTimesNzC v q w)
    vModR           = Module vAG (if cNzds then timesNzdsC else SV.timesC cR) vBDiv
    matAG           = SV.mkAG vAG
    matTimesV       = flip (SV.dotWith vAG timesNzC)
    isTrivial       = maxN == 0 || cIsZero cR.one
    matFlags        = if maxN == 1 then cFlags else RingFlags {
        commutative = isTrivial, noZeroDivisors = isTrivial, nzInverses = isTrivial }
    a *~ b          = SV.mapC SV.isZero (matTimesV a) b
    one             = diagNMat maxN cR.one
    fromZ z         = diagNMat maxN (cR.fromZ z)
    matRing         = Ring matAG matFlags (*~) one fromZ bDiv
    diagNMat n c    = if cIsZero c then SV.zero else
        SV.fromDistinctAscNzs [i :!: SV.fromNzIC i c | i <- [0 .. n - 1]]
    upperTriSolve m     = loop []
      where
    -- @@@:
        loop done v     = case SV.lastPairMaybe v of
            S.Nothing           -> SV.fromDistinctAscNzs done
            S.Just (i :!: c)    -> loop ((i :!: q) : done) v2
              where     -- want m * w2 = v2 => m * ((i :!: q), w2) = ((i :!: c), v1)
                col         = getCol m i
                j :!: d     = SV.lastPair col
                q           = assert (j == i) $ exactQuo cR c d
                v2          = minusTimesNzC v q col
    lowerTrDivBy m      = loop []
      where
        t   = S.maybe 0 S.fst (SV.lastPairMaybe m)
        loop done v     = case SV.headPairMaybe v of
            S.Nothing           -> end
            S.Just (i :!: c)    -> if i > t then end else
                let     -- want m * w2 + r = v2 => m * ((i :!: q), w2) + r = ((i :!: c), v1)
                    col         = getCol m i
                    j :!: d     = SV.headPair col
                    q           = assert (j == i) $ exactQuo cR c d
                    v2          = minusTimesNzC v q col
                in  loop ((i :!: q) : done) v2
          where
            ~end    = (SV.fromDistinctAscNzs (reverse done), v)
    lowerTriSolve m v   = assert (SV.isZero r) q
      where
        (q, r)  = lowerTrDivBy m v
    bDiv _doFull y _t       = (SV.zero, y) -- @@ improve (incl. solving linear equations in parallel)

transpose       :: Op1 (Matrix c)
transpose       = SV.foldBIMap' SV.concat SV.zero (\j -> SV.mapNzFC (SV.fromNzIC j))
