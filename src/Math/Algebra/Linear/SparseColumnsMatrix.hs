{-# LANGUAGE Strict #-}

{- |  A sparse columns 'Matrix' is implemented as a 'SV.Vector' of 'SV.Vector's or
    'SV.VectorU's.
    
    This data structure is also fairly efficient for dense matrices.
    
    This module uses LANGUAGE Strict. In particular, constructor fields and function arguments
    are strict unless marked with a ~. Also, a 'Matrix' or 'MatrixA' is strict in both its spine
    and its elements. Finally, "Data.Strict.Maybe" and "Data.Strict.Tuple" may be often used.
-}

module Math.Algebra.Linear.SparseColumnsMatrix (
    -- * Matrix
    MatrixA, Matrix, MatrixU,
    -- * Inlinable or worker-wrapper function(s)
    getCol,
    -- * Other functions
    PLUQMats(..), MatrixOps(..), matrixOps, transpose
) where

import Math.Algebra.General.Algebra
import Math.Algebra.Linear.SparseVector as SV

import qualified Data.Primitive.Contiguous as C
import Data.Primitive.PrimArray (PrimArray)
import Data.Primitive.SmallArray (SmallArray)
import qualified Data.Strict.Maybe as S
import qualified Data.Strict.Tuple as S
import Data.Strict.Tuple ((:!:), pattern (:!:))


-- * Matrix

type MatrixA arr c  = SV.Vector (SV.VectorA arr c)
{- ^ A matrix stored as columns, implementing a linear map between finitely generated right
    R-modules with basis elements indexed starting at 0. The columns are the images of the
    source module's basis elements. @(arr c)@ is a small array of nonzero @c@s. -}

type Matrix c   = MatrixA SmallArray c
-- ^ A matrix of boxed elements.

type MatrixU c  = VectorA PrimArray c
-- ^ A matrix of unboxed elements. A common example is integers modulo a single-word prime.

-- * Inlinable or worker-wrapper function(s)

getCol          :: C.Contiguous arr => MatrixA arr c -> Int -> SV.VectorA arr c
getCol          = SV.index SV.zero

-- * Other functions

data PLUQMats arr c     =
    PLUQMats { p :: Permute, l, u :: MatrixA arr c, q :: Permute, r :: Int }
{- ^ A matrix factorization @p * l * u * q@ where:
    
    * @p@ and @q@ are permutations
    * @l@ and @u@ are /lower/ and /upper trapezoidal/ respectively
        (@i \< j => l[i, j] = u[j, i] = 0@)
    * @0 \<= i \< r => l[i, i]@ and @u[i, i]@ are units
    * @r \<= i => l[j, i] = u[i, j] = 0@ for all @j@
    
    Descriptively, @l@ has @r@ columns and @u@ has @r@ rows, their main diagonal elements are
    units, and they are 0 before that. -}

{- |  @upperTriSolve m v@ returns the unique @w@ such that @m * w = v@. @m@ must be upper
    triangular (hence square), and its main diagonal elements must be units starting when @v@
    becomes nonzero. That is, if @v[i]@ is nonzero and @i \<= k@, then @m[k, k]@ must be a
    unit. (We also require @w@ to be zero before @v@ first becomes nonzero.)
    
    @lowerTrDivBy m v = (q, r) => v = m*q + r@ and @rows[0 .. t](r) = 0@; where @m@ is lower
    trapezoidal, has max column @t@, and its main diagonal elements are units starting when @v@
    becomes nonzero. That is, if @v[i]@ is nonzero and @i \<= k \<= t@, then @m[k, k]@ must be a
    unit.
    
    @lowerTriSolve m v@ returns the unique @w@ such that @m * w = v@. @m@ must be lower
    triangular, and its main diagonal elements must be units starting when @v@ becomes nonzero.
    That is, if @v[i]@ is nonzero and @i \<= k@, then @m[k, k]@ must be a unit. (We also require
    @w@ to be zero before @v@ first becomes nonzero.) -}
data MatrixOps arr c    = MatrixOps {
    vModR           :: ModR c (SV.VectorA arr c),
    matTimesV       :: MatrixA arr c -> Op1 (SV.VectorA arr c),
    matRing         :: Ring (MatrixA arr c),
    diagNMat        :: Int -> (Int -> c) -> MatrixA arr c,  -- ^ create a diagonal nxn matrix
    upperTriSolve   :: MatrixA arr c -> Op1 (SV.VectorA arr c),
    lowerTrDivBy    :: MatrixA arr c -> SV.VectorA arr c ->
                        (SV.VectorA arr c, SV.VectorA arr c),
    lowerTriSolve   :: MatrixA arr c -> Op1 (SV.VectorA arr c)
}
matrixOps       :: forall c arr. (C.Contiguous arr, C.Element arr c) =>
                    Ring c -> ModR c (VectorA arr c) -> Int -> MatrixOps arr c
{- ^ Ring of matrices. @one@ and @fromZ@ of @matrixOps cR vModR n@ will create @n x n@ matrices.
    @matRing.ag.monFlags.nontrivial@ assumes @n > 0@. -}
matrixOps cR vModR maxN     = MatrixOps { .. }
  where
    cIsZero         = cR.isZero
    vAG             = vModR.ag
    cFlags          = cR.rFlags
    timesNzC        = vModR.scale   -- use timesNzdCU when possible for speed
    minusTimesNzC v q w     = vAG.plus v $! timesNzC (cR.neg q) w
    matAG           = SV.mkAG vAG
    matTimesV       = flip (SV.dotWith vAG timesNzC)
    isTrivial       = maxN == 0 || cIsZero cR.one
    matFlags        = if maxN == 1 then cFlags else RingFlags {
        commutative = isTrivial, noZeroDivisors = isTrivial, nzInverses = isTrivial }
    a *~ b          = SV.mapC SV.isZero (matTimesV a) b
    one             = diagNMat maxN (const cR.one)
    fromZ z         = diagNMat maxN (const (cR.fromZ z))
    matRing         = Ring matAG matFlags (*~) one fromZ bDiv
    diagNMat n f    = SV.fromDistinctAscNzs
        [i :!: SV.fromNzIC i c | i <- [0 .. n - 1], let c = f i, not (cIsZero c)]
    upperTriSolve m     = loop []
      where
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
    lowerTriSolve m v   = if SV.isZero r then q else error "lowerTriSolve: illegal inputs"
      where
        (q, r)  = lowerTrDivBy m v
    bDiv _doFull y _t       = (SV.zero, y) -- @@ improve (incl. solving linear equations in parallel)
{-# SPECIALIZE matrixOps :: Ring c -> ModR c (Vector c) -> Int -> MatrixOps SmallArray c #-}

transpose       :: (C.Contiguous arr, C.Element arr c) => Op1 (MatrixA arr c)
-- ^ Transpose an mxn matrix into an nxm one, swapping elements (i, j) and (j, i).
transpose       = SV.foldBIMap' (SV.unionWith (const False) SV.join) SV.zero
                    (SV.mapNzFC . SV.fromNzIC)
{-# SPECIALIZE transpose :: Op1 (Matrix c) #-}
