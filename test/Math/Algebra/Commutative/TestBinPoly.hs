{- |  This module tests the "BinPoly" module.  -}

module Math.Algebra.Commutative.TestBinPoly (
    testBinPoly
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.BinPoly

import Math.Algebra.General.TestAlgebra

import Hedgehog (Property, PropertyName, (===), annotate, annotateShow, assert, forAll,
    withTests)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Bits (bit)
import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import Data.Tuple.Extra (second)
import Data.Word (Word64)
import qualified StrictList2 as SL


-- @@ move and generalize through 'groebnerBasisProps':
allPT               :: (a -> String) -> Pred a -> [a] -> PropertyIO ()
allPT aShow p as    = do
    annotate $ listShowWith aShow as
    annotateShow $ map p as
    assert (all p as)

groebnerBasisProps      :: ShowGen p -> GBPolyOps ev term p -> [(PropertyName, Property)]
groebnerBasisProps pSG gbpA@(GBPolyOps { .. })  = [("GB Residues 0", residues0)]
  where
    gsSG            = listShowGen (Range.linear 0 10) pSG
    gbTrace         = 0
    scale11         = Gen.scale (Range.Size 11 *)
    sPolyIJ gs i j  = sPoly f g (SPair i j (evTotDeg m) m)
      where
        f   = Seq.index gs i
        g   = Seq.index gs j
        m   = evLCM (leadEvNZ f) (leadEvNZ g)
    residues0       = withTests 10 $ property $ do
        initGens        <- genVis (second scale11 gsSG)
        nCores          <- forAll (scale11 (Gen.int (Range.linear 1 4)))
        doRedGens       <- forAll (scale11 Gen.bool)
        doFullMod       <- forAll (scale11 Gen.bool)
        let SubmoduleOps { .. }     = gbiSmOps gbpA nCores gbTrace
            gbIdeal         = fromGens initGens
            gbGens          = stdGens doRedGens gbIdeal
            gbGensL         = toList gbGens
            checkZeros ps   = allPT pShow (rIsZero pR) (map (\p -> bMod doFullMod p gbIdeal) ps)
        annotate $ fst gsSG gbGensL
        checkZeros initGens
        mapM_ checkZeros
            [[sPolyIJ gbGens i j | i <- [0 .. j - 1]]
                | j <- [1 .. length gbGens - 1]]

boolField       :: Field Bool   -- Z/2Z, where 1 is True
boolField       = field (Group agFlags (==) (/=) False not id) (&&) True odd id

type BP58       = BinPoly EV58
type BP58Ops    = (GBPolyOps EV58 EV58 BP58, BPOtherOps EV58 Word64)

gbCountZerosProp                    :: ShowGen BP58 -> BP58Ops -> (PropertyName, Property)
gbCountZerosProp pSG (gbpA, bpoA)   = ("gbCountZeros", gbCountZeros)
  where
    gsSG            = listShowGen (Range.linear 0 10) pSG
    gbTrace         = 0
    scale11         = Gen.scale (Range.Size 11 *)
    gbCountZeros    = withTests 10 $ property $ do
        initGens        <- genVis (second scale11 gsSG)
        nCores          <- forAll (scale11 (Gen.int (Range.linear 1 4)))
        let SubmoduleOps { .. }     = gbiSmOps gbpA nCores gbTrace
            gbIdeal         = fromGens initGens
            reducedGensL    = toList (stdGens True gbIdeal)
        annotate $ fst gsSG reducedGensL
        bpCountZeros bpoA initGens === bpCountZeros bpoA reducedGensL

test1           :: Int -> StdEvCmp -> IO Bool
-- 1 <= nVars <= 58
test1 nVars sec = checkGroup ("BinPoly " ++ show nVars ++ " " ++ show sec) props
  where
    evCmp           = evCmp58 sec
    isGraded        = secIsGraded sec
    xVarSs          = ['X' : show n | n <- [1 :: Int ..]]
    varSs           = take nVars (map (: []) ['a' .. 'z'] ++ xVarSs)
    bpA2@(gbpA@(GBPolyOps { evShow, pR, pShow }), BPOtherOps { bpVar, pAt })    =
        bp58Ops evCmp isGraded varSs
    varPs           = map bpVar [0 .. nVars - 1]
    mask            = bit nVars - 1     :: Word64
    vals            = 0x6789abcdef012345 .&. mask
    -- evTestEq        = diffWith evShow (==)
    evGen           = fmap fromBits58 (Gen.word64 (Range.linear 0 mask))
    evSG            = (evShow, evGen)
    pTestEq         = diffWith pShow (==)
    monomGen        = fmap SL.singleton evGen
    pSG             = (pShow, fmap (rSumL' pR) (Gen.list (Range.linear 0 10) monomGen))
    pToT p          = pAt p vals
    gbProps         = if nVars > 6 then [] else
                        groebnerBasisProps pSG gbpA ++ [gbCountZerosProp pSG bpA2]
    
    props           = totalOrderProps evSG (==) evCmp
                        ++ withRing pR ringProps pSG pTestEq (eiBit IsCommutativeRing)
                        ++ ringHomomProps pSG pR (===) boolField pToT
                        ++ [readsProp pSG pTestEq (polynomReads pR (zip varSs varPs))]
                        ++ gbProps

testBinPoly             :: IO Bool
testBinPoly             =
    checkAll $ checkGroup "boolField" (withRing boolField fieldProps (show, Gen.bool) (===))
        : [test1 nVars sec
            | nVars <- [1 .. 6] ++ [14, 25 .. 58], sec <- [LexCmp, GrLexCmp, GrRevLexCmp]]
