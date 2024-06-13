{- |  This module helps test the "Math.Algebra.Commutative.GroebnerBasis" module and its
    clients.  -}

module Math.Algebra.Commutative.TestGroebnerBasis (
    groebnerBasisTests
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.GroebnerBasis

import Math.Algebra.General.TestAlgebra

import Hedgehog ((===), forAll, withTests)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Foldable (toList)
import qualified Data.RRBVector as GBV


groebnerBasisTests      :: GBPoly ev term p => GBPolyOps ev p -> ShowGen [p] -> ([p] -> Int) ->
                            TestTree
-- currently checks original gens & s-pairs reduce to 0 using 'bModBy'; TODO add a bDivBy and
-- test it & bModBy, and test the stdGens are in the original ideal
{-# INLINABLE groebnerBasisTests #-}
groebnerBasisTests gbpA@(GBPolyOps { .. }) halfInitGensSG countZeros    =
    testWith "Groebner Bases" (withTests 10) gbTM
  where
    scale11         = Gen.scale (Range.Size 11 *)
    gsSG11          = halfInitGensSG { gen = scale11 halfInitGensSG.gen }
    sPolyIJ gs i j  = sPoly f g (SPair i j (evTotDeg m) m (const undefined))
      where
        f   = gs GBV.! i
        g   = gs GBV.! j
        m   = evLCM nVars (leadEvNz f) (leadEvNz g)
    gbTrace         = 0
    gbTM            = do
        gens0           <- genVis gsSG11
        gens1           <- genVis gsSG11
        -- nCores          <- forAll (scale11 (Gen.int (Range.linear 1 4)))
        doRedGens       <- forAll (scale11 (IsDeep <$> Gen.bool))
        doFullMod       <- forAll (scale11 (IsDeep <$> Gen.bool))
        let smA@(SubmoduleOps { .. })   = gbiSmOps gbpA
            gbIdeal         = plusGens gbTrace (fromGens smA gbTrace gens0) gens1
            gbGens          = stdGens doRedGens gbIdeal
            gbGensL         = toList gbGens
            checkRes0s ps   = allTM pShowPrec pR.isZero (map (bModBy doFullMod gbIdeal) ps)
        annotateB $ gsSG11.tSP gbGensL
        checkRes0s (gens0 ++ gens1)
        mapM_ checkRes0s
            [[sPolyIJ gbGens i j | i <- [0 .. j - 1]]
                | j <- [1 .. length gbGens - 1]]
        countZeros (gens0 ++ gens1) === countZeros gbGensL
