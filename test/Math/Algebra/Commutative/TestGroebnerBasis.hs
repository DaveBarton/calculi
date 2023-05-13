{- |  This module helps test the "GroebnerBasis" module and its clients.  -}

module Math.Algebra.Commutative.TestGroebnerBasis (
    groebnerBasisProps
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.GroebnerBasis

import Math.Algebra.General.TestAlgebra

import Hedgehog (Property, PropertyName, (===), annotate, forAll, withTests)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Foldable (toList)
import qualified Data.Sequence as Seq


groebnerBasisProps      :: GBPoly ev term pf p => GBPolyOps ev p -> ShowGen [p] ->
                            ([p] -> Int) -> [(PropertyName, Property)]
-- currently checks original gens & s-pairs reduce to 0 using 'bModBy'; TODO add a bDivBy and
-- test it & bModBy, and test the stdGens are in the original ideal
{-# INLINABLE groebnerBasisProps #-}
groebnerBasisProps gbpA@(GBPolyOps { .. }) halfInitGensSG countZeros    =
    [("Groebner Bases", gbProp)]
  where
    scale11         = Gen.scale (Range.Size 11 *)
    gsSG11          = halfInitGensSG { gen = scale11 halfInitGensSG.gen }
    sPolyIJ gs i j  = sPoly f g (SPair i j (evTotDeg m) m)
      where
        f   = Seq.index gs i
        g   = Seq.index gs j
        m   = evLCM nVars (leadEvNZ f) (leadEvNZ g)
    gbTrace         = 0
    gbProp          = withTests 10 $ property $ do
        gens0           <- genVis gsSG11
        gens1           <- genVis gsSG11
        nCores          <- forAll (scale11 (Gen.int (Range.linear 1 4)))
        doRedGens       <- forAll (scale11 (IsDeep <$> Gen.bool))
        doFullMod       <- forAll (scale11 (IsDeep <$> Gen.bool))
        let smA@(SubmoduleOps { .. })   = gbiSmOps gbpA nCores
            gbIdeal         = plusGens gbTrace (fromGens smA gbTrace gens0) gens1
            gbGens          = stdGens doRedGens gbIdeal
            gbGensL         = toList gbGens
            checkRes0s ps   = allPT pShow pR.isZero (map (bModBy doFullMod gbIdeal) ps)
        annotate $ gsSG11.tShow gbGensL
        checkRes0s (gens0 ++ gens1)
        mapM_ checkRes0s
            [[sPolyIJ gbGens i j | i <- [0 .. j - 1]]
                | j <- [1 .. length gbGens - 1]]
        countZeros (gens0 ++ gens1) === countZeros gbGensL
