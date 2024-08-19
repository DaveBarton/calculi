{- |  This module helps test the "Math.Algebra.Linear.SparseVector" module and its clients.
    
    This module is normally imported qualified.  -}

module Math.Algebra.Linear.TestSparseVector (
    testOpsAG, tests
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
import Data.Maybe (fromMaybe)
import qualified Data.Primitive.Contiguous as C
import Data.Strict.Classes (toLazy, toStrict)
import qualified Data.Strict.Maybe as S
import qualified Data.Strict.Tuple as S
import Data.Strict.Tuple ((:!:), pattern (:!:))
import qualified Data.Text as T


sJustIf         :: Bool -> a -> S.Maybe a
-- like 'Control.Monad.Extra.pureIf'
sJustIf b ~a    = if b then S.Just a else S.Nothing

nToText26       :: Integral n => n -> Text
-- Convert to one of 26 simple text values.
nToText26 n     = T.singleton (toEnum (fromEnum 'a' + fromIntegral n `mod` 26))


testOpsAG       :: (C.Contiguous arr, C.Element arr c, Show (SV.VectorA arr c)) =>
                    AbelianGroup c ->
                    Range Int -> TestOps Int -> TestOps c -> TestOps (SV.VectorA arr c)
-- ^ @testOpsAG cAG sumRange iTA cTA@. The caller tests @cAG@.
testOpsAG cAG sumRange iTA cTA  = TestOps tSP tCheck gen vAG.eq
  where
    tSP             = SV.showPrec iTA.tSP cTA.tSP
    tCheck notes v  = do
        SV.iFoldL (\_i _ c -> cTA.tCheck notes1 c) (pure ()) v  -- show i on failure?
        tCheckBool (errs ++ notes1) (null errs)
      where
        notes1  = {- (tSP v).t -} showT v : notes
        errs    = SV.check (const cAG.isZero) v
    vAG             = SV.mkAG cAG
    iCToV           = SV.fromPIC cAG.isZero
    gen             = sumL' vAG <$> Gen.list sumRange (liftA2 iCToV iTA.gen cTA.gen)

type C          = Int
type V          = SV.Vector C   -- the main type for testing SparseVector.hs
type H          = Int           -- V maps almost injectively to H
type VL         = [Int :!: C]   -- only DistinctAscNzs; V->VL->V == id, so VL->V is a surjection
type IM         = IM.IntMap C   -- only nonzero terms; V->IM->V == id
type VU         = SV.VectorU C  -- isomorphic to V as right modules over C

tests           :: TestTree
-- ^ Test the "Math.Algebra.Linear.SparseVector" module.
tests           = testGroup "SparseVector" testsL
  where
    cAG             = intRing.ag
    largeInts       = take 6 $ iterate (`quot` 2) (maxBound :: Int)
    iTA             = numVarTestOps "u" (Gen.frequency  -- index test ops
        [(10, Gen.int (Range.exponential 0 1_000_000)), (1, Gen.element largeInts)])
    cTA             = testOps0 (Gen.int (Range.exponentialFrom 0 minBound maxBound))
    vTA             = testOpsAG cAG (Range.linear 0 20) iTA cTA     :: TestOps V
    vAG             = SV.mkAG cAG   :: AbelianGroup V
    vToH            :: V -> H   -- a homomorphism of right modules over C
    iCToH i c       = (3 * i `rem` 101 + 5) * c
    vToH            = SV.foldBIMap' (+) 0 iCToH
    
    vToIM           = IM.fromDistinctAscList . map toLazy . SV.toDistinctAscNzs
    imNzsToV        = SV.fromDistinctAscNzs . map toStrict . IM.toAscList
    vToVU           = SV.mapNzFC id     :: V -> VU
    vuToV           = SV.mapNzFC id     :: VU -> V
    
    testViaH        :: V -> H -> TestM ()   -- tAnnotate v, and check it maps to h
    testViaH        = tImageEq vTA (===) vToH
    testViaL        :: TestRel b -> (V -> b) -> (VL -> b) -> TestM ()   -- test the (V -> b)
    testViaL bTestEq f okF  = sameFun1TR vTA bTestEq f (okF . SV.toDistinctAscNzs)
    testEqToVL      :: V -> VL -> TestM ()
    testEqToVL w okDANzs    = vTA.tEq w (SV.fromDistinctAscNzs okDANzs)
    testViaIM       :: TestRel b -> (V -> b) -> (IM -> b) -> TestM ()   -- test the (V -> b)
    testViaIM bTestEq f okF = sameFun1TR vTA bTestEq f (okF . vToIM)
    
    sJustNz c       = sJustIf (c /= 0) c
    
    fromICTest      = singleTest "fromIC" $ do  -- test fromPIC, fromIMaybeC, fromNzIC
        i       <- genVis iTA
        c       <- genVis cTA
        when (c /= 0) $ testViaH (SV.fromNzIC i c)  (iCToH i c)
        testViaH (SV.fromPIC cAG.isZero i c)        (iCToH i c)
        testViaH (SV.fromIMaybeC i (sJustNz c))     (iCToH i c)
    distinctAscNzsTest  = singleTest "distinctAscNzs" $ do
        -- test toDistinctAscNzs, fromDistinctAscNzs
        v           <- genVis vTA
        let vL      = SV.toDistinctAscNzs v
        annotateB (listShowPrec (sPairShowPrec iTA.tSP cTA.tSP) vL)
        tCheckBool ["Zero coordinate"] $ all ((/= 0) . S.snd) vL
        tCheckBool ["Not strictly ascending"] $ isSortedBy ((<) `on` S.fst) vL
        vTA.tEq (sumL' vAG (map (S.uncurry SV.fromNzIC) vL)) v
        vTA.tEq (SV.fromDistinctAscNzs vL) v
    -- TODO: test fromDistinctNzs
    indexTest       = singleTest "index, indexMaybe, split, join" $ do
        v       <- genVis vTA
        i       <- genVis (testOps0 (Gen.int (Range.exponential 0 10_000)))
        let vL  = SV.toDistinctAscNzs v
            mc  = lookup i (map toLazy vL)
        SV.index 0 v i === fromMaybe 0 mc
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
        iNNToN          :: Int -> Op2 C
        iNNToN i m n    = 2 * i + m - n
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
        let iCToMC i c  = sJustNz ((i + c) `rem` 3)
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
    plusUTest       = singleTest "plusU" $
        sameFunAABTR vTA vTA.tEq (vuToV .* SV.plusU `on` vToVU) vAG.plus
    -- TODO: test unionDisj
    vApplyTest      = singleTest "vApply" $ sameFunAABTR vTA vTA.tEq (SV.vApply iDMcToMc) okF
      where
        iDMcToC i d mc  = (i + 2 * d + 3 * S.fromMaybe 5 mc) `rem` 7
        iDMcToMc i d    = sJustNz . iDMcToC i d
        iDCToMc i d     = toLazy . iDMcToMc i d . S.Just
        dIMToCIM        = IM.filter (/= 0) . IM.mapWithKey (\i d -> iDMcToC i d S.Nothing)
        mergeIM         = IM.mergeWithKey iDCToMc dIMToCIM id
        okF             = imNzsToV .* mergeIM `on` vToIM
    -- TODO: test foldLIntersect'
    -- TODO: test mkAGU
    dotWithTest     = singleTest "dotWith" $ sameFunAABTR vTA (===) (SV.dotWith cAG mult) okF
      where
        mult c d        = c * (d `quot` 2)  -- noncommutative
        okF v           = SV.foldBIMap' (+) 0 (\i c -> SV.index 0 v i `mult` c)
    timesCsTest     = singleTest "timesNzdC, timesNzdCU, timesC" $ do
        v       <- genVis vTA
        c       <- genVis cTA
        let vcH     = vToH v * c
        when (odd c) $ do
            testViaH        (SV.timesNzdC intRing c v)          vcH
            testViaH (vuToV (SV.timesNzdCU        c (vToVU v))) vcH
        testViaH            (SV.timesC    intRing c v)          vcH
        -- TODO: test over a noncommutative ring also, using a right-linear map for vToH
    -- TODO: test monicizeUnit, e.g. using Z mod p or Q
    -- TODO: test mkModR, mkModRU
    {- TODO: test Permute section
    vPComposeTest   = singleTest "vPCompose" $ do
        v       <- genVis vTA
        pv      <- SV.mapNzFC abs1 <$> genVis vTA
        vTA.tEq (SV.vPCompose v (SV.OrId pv)) ((imNzsToV .* vPComposeIM `on` vToIM) v pv)
      where
        abs1 n              = if n == minBound then 1 else abs n
        vPComposeIM vm pm   = IM.compose vm (IM.union pm (IM.mapWithKey (\i _ -> i) vm)) -}
    swapTest        = singleTest "swap" $ do
        v       <- genVis vTA
        i       <- genVis iTA
        j       <- genVis iTA
        let swapIJ k    = if k == i then j else if k == j then i else k
        vTA.tEq (SV.swap i j v) (imNzsToV (IM.mapKeys swapIJ (vToIM v)))
    -- TODO: test showPrec
    
    testsL          = [
        singleTest "not eq, vToH" $ almostInjectiveTM vTA (==) vToH,
        -- testViaH is now valid
        singleTest "plus" $ homomTM vTA vAG.plus (===) (+) vToH,
        abelianGroupTests vTA (IsNontrivial True) vAG,
        -- vAG has now been tested (by the above lines), so vTA.gen and vTA.eq have been also
        testOnce "zero" $ vTA.tEq SV.zero vAG.zero, fromICTest, distinctAscNzsTest,
        -- testViaL, testEqToVL, vToIM, imToV, vToIM, imNzsToV, and testViaIM are now valid
        singleTest "isZero" $ testViaL (===) SV.isZero null,
        singleTest "size"   $ testViaL (===) SV.size length,
        singleTest "headPairMaybe"  $
            testViaIM (===) SV.headPairMaybe (toStrict . (toStrict <$>) . IM.lookupMin),
        singleTest "lastPairMaybe"  $
            testViaIM (===) SV.lastPairMaybe (toStrict . (toStrict <$>) . IM.lookupMax),
        indexTest, headLastTest, foldsTest, mapsTest,
        -- vToVU and vuToV are now valid
        unionTest, plusUTest, vApplyTest, dotWithTest, timesCsTest,
        swapTest
        ]
