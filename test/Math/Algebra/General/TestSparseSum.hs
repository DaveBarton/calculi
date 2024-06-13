{- |  This module helps test the "Math.Algebra.General.SparseSum" module and its clients.  -}

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


ssTestOps               :: AbelianGroup c -> Cmp d ->
                            Range Int -> TestOps c -> TestOps d -> TestOps (SparseSum c d)
-- ^ The caller tests @cAG@ and @dCmp@, including that @dCmp@ gives a total order.
ssTestOps cAG dCmp sumRange cTA dTA     = TestOps tSP tCheck gen ssAG.eq
  where
    UnivL ssAG (TgtArrsF dcToSS) _univF     = ssAGUniv cAG dCmp
    cdTA            = TestOps cdSP cdTCheck undefined undefined
    cdSP cd         = infixPT multPrec " " (cTA.tSP cd.c) (dTA.tSP cd.d)    -- always show c & d
    cdTCheck notes cd   = do
        cTA.tCheck notes1 cd.c
        dTA.tCheck notes1 cd.d
        tCheckBool ((cdSP cd).t : notes) (not (cAG.isZero cd.c))
      where
        notes1  = (ssTermShowPrec dTA.tSP cTA.tSP cd).t : notes
    slTA            = slTestOps undefined cdTA
    tSP             = ssShowPrec dTA.tSP cTA.tSP
    tCheck notes s  = do
        slTA.tCheck notes s
        tCheckBool ((tSP s).t : notes) (isSortedBy ((== GT) .* dCmp `on` (.d)) (toList s))
    gen             = sumL' ssAG <$> Gen.list sumRange (liftA2 dcToSS dTA.gen cTA.gen)
