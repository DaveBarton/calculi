{- |  This module helps test the "Math.Algebra.Linear.SparseVector" module and its clients.
    
    This module is normally imported qualified.  -}

module Math.Algebra.Linear.TestSparseVector (
    testOps, tests
) where

import Math.Algebra.General.Algebra hiding (assert)
import qualified Math.Algebra.Linear.SparseVector as SV

import Math.Algebra.General.TestAlgebra

import Hedgehog (discard)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Monad (when)
import Data.Bifunctor (second)
import qualified Data.IntMap.Strict as IM
import Data.Strict.Classes (toLazy, toStrict)
import qualified Data.Strict.Maybe as S
import qualified Data.Strict.Tuple as S
import Data.Strict.Tuple ((:!:), pattern (:!:))
import qualified Data.Text as T
import Safe (headMay, lastMay)  -- @@@ or use IntMap lookupMin, lookupMax and toStrict, remove 'safe' dependency


sJustIf         :: Bool -> a -> S.Maybe a
-- like 'Control.Monad.Extra.pureIf'
sJustIf b ~a    = if b then S.Just a else S.Nothing

nToText26       :: Integral n => n -> Text
-- Convert to one of 26 simple text values.
nToText26 n     = T.singleton (toEnum (fromEnum 'a' + fromIntegral n `mod` 26))


testOps         :: AbelianGroup c -> Range Int -> TestOps Int -> TestOps c ->
                    TestOps (SV.Vector c)
-- ^ @testOps cAG sumRange iTA cTA@. The caller tests @cAG@.
testOps cAG sumRange iTA cTA    = TestOps tSP tCheck gen vAG.eq
  where
    tSP             = SV.showPrec iTA.tSP cTA.tSP
    tCheck notes v  = do
        SV.iFoldL (\_i _ c -> cTA.tCheck notes1 c) (pure ()) v  -- show i on failure?
        tCheckBool (errs ++ notes1) (null errs)
      where
        notes1  = (tSP v).t : notes
        errs    = SV.check cAG.isZero v
    vAG             = SV.mkAG cAG
    iCToV           = SV.fromPIC cAG.isZero
    gen             = sumL' vAG <$> Gen.list sumRange (liftA2 iCToV iTA.gen cTA.gen)

type V          = SV.Vector Integer     -- the main type for testing SparseVector.hs
type Y          = Int                   -- V maps almost injectively to Y
type VL         = [Int :!: Integer]     -- only DistinctAscNzs; V->VL->V == id, so VL->V is a
                                            -- surjection
-- type IM         = IM.IntMap             -- only nonzero terms; V->IM->V == id

tests           :: TestTree
-- ^ Test the "Math.Algebra.Linear.SparseVector" module.
tests           = testGroup "SparseVector" testsL
  where
    cAG             = zzAG
    largeInts       = take 6 $ iterate (`quot` 2) (maxBound :: Int)
    iTA             = numVarTestOps "u" (Gen.frequency
        [(10, Gen.int (Range.exponential 0 1_000_000)), (1, Gen.element largeInts)])
    cTA             = zzTestOps { gen = zzExpGen 200 }
    vTA             = testOps cAG (Range.linear 0 20) iTA cTA
    vAG             = SV.mkAG cAG
    vToY            :: V -> Y
    iCToY i c       = (3 * i `rem` 101 + 5) * fromIntegral c
    vToY            = SV.foldBIMap' (+) 0 iCToY
    
    vToIM           = IM.fromDistinctAscList . map toLazy . SV.toDistinctAscNzs
    imNzsToV        = SV.fromDistinctAscNzs . map toStrict . IM.toAscList
    
    testViaY        :: V -> Y -> TestM ()   -- tAnnotate v, and check it maps to u
    testViaY        = tImageEq vTA (===) vToY
    testViaL        :: TestRel b -> (V -> b) -> (VL -> b) -> TestM ()   -- test the (V -> b)
    testViaL bTestEq f okF  = sameFun1TR vTA bTestEq f (okF . SV.toDistinctAscNzs)
    testEqToVL      :: V -> VL -> TestM ()
    testEqToVL w okDANzs    = vTA.tEq w (SV.fromDistinctAscNzs okDANzs)
    
    fromICTest      = singleTest "fromIC" $ do  -- test fromPIC, fromIMaybeC, fromNzIC
        i       <- genVis iTA
        c       <- genVis cTA
        when (c /= 0) $ testViaY (SV.fromNzIC i c)       (iCToY i c)
        testViaY (SV.fromPIC cAG.isZero i c)             (iCToY i c)
        testViaY (SV.fromIMaybeC i (sJustIf (c /= 0) c)) (iCToY i c)
    distinctAscNzsTest  = singleTest "distinctAscNzs" $ do
        -- test toDistinctAscNzs, fromDistinctAscNzs
        v           <- genVis vTA
        let vL      = SV.toDistinctAscNzs v
        annotateB (listShowPrec (sPairShowPrec iTA.tSP cTA.tSP) vL)
        tCheckBool ["Zero coordinate"] $ all ((/= 0) . S.snd) vL
        tCheckBool ["Not strictly ascending"] $ isSortedBy ((<) `on` S.fst) vL
        vTA.tEq (sumL' vAG (map (S.uncurry SV.fromNzIC) vL)) v
        vTA.tEq (SV.fromDistinctAscNzs vL) v
    indexTest       = singleTest "index, indexMaybe, split, join" $ do
        v       <- genVis vTA
        i       <- genVis (testOps0 (Gen.int (Range.exponential 0 10_000)))
        let vL  = SV.toDistinctAscNzs v
            mc  = lookup i (map toLazy vL)
        SV.index 0 v i === maybe 0 id mc
        SV.indexMaybe v i === toStrict mc
        let (v0 :!: v1)     = SV.split i v
        testEqToVL v0 (filter ((<  i) . S.fst) vL)
        testEqToVL v1 (filter ((>= i) . S.fst) vL)
        vTA.tEq (SV.join v0 v1) v
    headLastTest    = singleTest "headPair, lastPair" $ do
        v       <- genVis vTA
        when (SV.isZero v) discard
        SV.headPair v === S.fromJust (SV.headPairMaybe v)
        SV.lastPair v === S.fromJust (SV.lastPairMaybe v)
    foldsTest       = testGroup "folds" [iFoldRTest, iFoldLTest, foldBIMap'Test]
      where
        iNNToN          :: Int -> Op2 Integer
        iNNToN i m n    = 2 * fromIntegral i + m - n
        iFoldRTest      = singleTest "iFoldR" $
            testViaL (===) (SV.iFoldR iNNToN 100) (foldr (S.uncurry iNNToN) 100)
        iFoldLTest      = singleTest "iFoldL" $
            testViaL (===) (SV.iFoldL iNNToN 100) (foldl (\t (i :!: c) -> iNNToN i t c) 100)
        iCToT i c       = T.replicate (i `rem` 3) (nToText26 c)
        foldBIMap'Test  = singleTest "foldBIMap'" $
            testViaL (===) (SV.foldBIMap' (<>) "" iCToT) (foldMap (S.uncurry iCToT))
    mapsTest        = singleTest "maps" $ do    -- mapC, mapNzFC, mapCMaybeWithIndex
        v               <- genVis vTA
        let vL          = SV.toDistinctAscNzs v
        testEqToVL (SV.mapC (== 0) (`rem` 3) v)
            (filter ((/= 0) . S.snd) (map (second (`rem` 3)) vL))
        testEqToVL (SV.mapNzFC (3 *) v) (map (second (3 *)) vL)
        let iCToMC i c  = sJustIf (c' /= 0) c'
              where
                c'          = (fromIntegral i + c) `rem` 3
            pToMP (i :!: c)     = (i :!:) <$> iCToMC i c
        testEqToVL (SV.mapCMaybeWithIndex iCToMC v) (S.catMaybes (map pToMP vL))
    unionTest       = singleTest "unionWith" $ do
        v               <- genVis vTA
        w               <- genVis vTA
        let f m n       = (m + n + m * m * n) `rem` (abs (m + n) + 1)
            vIM         = vToIM v
            wIM         = vToIM w
        vTA.tEq (SV.unionWith (== 0) f v w)
            (imNzsToV (IM.filter (/= 0) (IM.unionWith f vIM wIM)))
    -- @@@ incl. tCheck/tAnnotate intermediate values from here on:
    -- vApply, invPermute, swap; 4 mult; showPrec?
    -- :@@@
    
    testsL          = [
        singleTest "not eq, vToY" $ almostInjectiveTM vTA (==) vToY,
        -- testViaY is now valid
        singleTest "plus" $ homomTM vTA vAG.plus (===) (+) vToY,
        abelianGroupTests vTA (IsNontrivial True) vAG,
        -- vAG has now been tested (by the above lines), so vTA.gen and vTA.eq have been also
        testOnce "zero" $ vTA.tEq SV.zero vAG.zero, fromICTest, distinctAscNzsTest,
        -- testViaL, testEqToVL, vToIM, and imToV are now valid
        singleTest "isZero" $ testViaL (===) SV.isZero null,
        singleTest "size"   $ testViaL (===) SV.size length,
        singleTest "headPairMaybe"  $ testViaL (===) SV.headPairMaybe (toStrict . headMay),
        singleTest "lastPairMaybe"  $ testViaL (===) SV.lastPairMaybe (toStrict . lastMay),
        indexTest, headLastTest, foldsTest, mapsTest, unionTest
        ]
