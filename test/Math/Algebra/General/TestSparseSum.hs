{- |  This module helps test the "SparseSum" module and its clients.  -}

module Math.Algebra.General.TestSparseSum (
    ssTestOps
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum

import Math.Algebra.General.TestAlgebra

import Hedgehog ()
import qualified Hedgehog.Gen as Gen
-- import qualified Hedgehog.Range as Range

import Data.Foldable (toList)


ssTestOps               :: forall c d. AbelianGroup c -> Cmp d ->
                            Range Int -> TestOps c -> TestOps d -> TestOps (SparseSum c d)
-- ^ The caller tests @cAG@ and @dCmp@, including that @dCmp@ gives a total order.
ssTestOps cAG dCmp sumRange cT dT   = TestOps tSP tCheck gen ssAG.eq
  where
    UnivL ssAG (TgtArrsF dcToSS) _univF     = ssAGUniv cAG dCmp
    cdT             = TestOps cdSP cdTCheck undefined undefined
    cdSP _prec cd   = cT.tShow cd.c ++ " " ++ dT.tShow cd.d
    cdTCheck notes cd   = do
        cT.tCheck notes1 cd.c
        dT.tCheck notes1 cd.d
        tCheckBool (cdSP 0 cd : notes) (not (cAG.isZero cd.c))
      where
        notes1  = ssTermShowPrec dT.tSP cT.tSP 0 cd : notes
    slT             = slTestOps undefined cdT
    tSP             = ssShowPrec dT.tSP cT.tSP
    tCheck notes s  = do
        slT.tCheck notes s
        tCheckBool (tSP 0 s : notes) (isSortedBy ((== GT) .* dCmp `on` (.d)) (toList s))
    gen             = sumL' ssAG <$> Gen.list sumRange (liftA2 dcToSS dT.gen cT.gen)
