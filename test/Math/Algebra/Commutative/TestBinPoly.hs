{- |  This module tests the "Math.Algebra.Commutative.BinPoly" module.  -}

module Math.Algebra.Commutative.TestBinPoly (
    binPolyTests
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.BinPoly

import Math.Algebra.General.TestAlgebra
import Math.Algebra.Commutative.TestGroebnerBasis

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Bits ((.&.), bit)
import Data.Foldable (toList)
import Data.Word (Word64)
import qualified StrictList2 as SL


boolField       :: Field Bool   -- Z/2Z, where 1 is True
boolField       =
    field (AbelianGroup (agFlags (IsNontrivial True)) (==) (/=) False not id) (&&) True odd id

test1           :: Int -> StdEvCmp -> TestTree
-- 1 <= nVars <= 58
test1 nVars sec = testGroup ("BinPoly " ++ show nVars ++ " " ++ show sec) testsL
  where
    evCmp           = evCmp58 sec
    isGraded        = secIsGraded sec
    xVarSs          = ['X' : show n | n <- [1 :: Int ..]]
    descVarSs       = take nVars (map (: []) ['a' .. 'z'] ++ xVarSs)
    useSugar        = UseSugar False    -- @@ change to use Gen.bool
    (gbpA@(GBPolyOps { evShowPrec, pR, descVarPs }), bpoA@(BPOtherOps { pAt, pShowPrec }))  =
        bp58Ops evCmp isGraded descVarSs useSugar
    mask            = bit nVars - 1     :: Word64
    vals            = 0x6789abcdef012345 .&. mask
    evTCheck notes v    = tCheckBool (show v : notes) (fromBits58 (toBits58 v) == v)
    evGen           = fmap fromBits58 (Gen.word64 (Range.linear 0 mask))
    evT             = TestOps evShowPrec evTCheck evGen (==)
    slT             = slTestOps undefined evT
    pTCheck notes p = do
        slT.tCheck notes p
        tCheckBool (pShowPrec 0 p : notes) (isSortedBy ((== GT) .* evCmp) (toList p))
    pGen            = rSumL' pR <$> Gen.list (Range.linear 0 10) (SL.singleton <$> evGen)
    pT              = TestOps pShowPrec pTCheck pGen (==)
    pToT p          = pAt p vals
    gbTestsL        = [groebnerBasisTests gbpA (listTestOps (Range.linear 0 5) pT)
                        (bpCountZeros bpoA) | nVars <= 6]
    reqFlags        =
        RingFlags { commutative = True, noZeroDivisors = False, nzInverses = False }
    
    testsL          = [totalOrderTests evT (==) (IsNontrivial True) evCmp,
                        ringTests pT (IsNontrivial True) reqFlags pR,
                        ringHomomTests (Just "Ring Homomorphism to Bool") pT pR (===)
                            boolField pToT,
                        readsTest pT (polynomReads pR (zip descVarSs descVarPs))]
                        ++ gbTestsL

binPolyTests            :: TestTree
binPolyTests            =
    testGroup "BinPoly" $ testGroup "boolField" [fieldTests (testOps0 Gen.bool) boolField]
        : [test1 nVars sec
            | nVars <- [1 .. 6] ++ [14, 25 .. 58], sec <- [LexCmp, GrLexCmp, GrRevLexCmp]]
