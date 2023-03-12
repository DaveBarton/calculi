{- |  This module tests the "BinPoly" module.  -}

module Math.Algebra.Commutative.TestBinPoly (
    testBinPoly
) where

import Math.Algebra.General.Algebra hiding (assert)
import Math.Algebra.Commutative.GroebnerBasis (GBPolyOps(..))
import Math.Algebra.Commutative.BinPoly

import Math.Algebra.General.TestAlgebra

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Data.Bits (bit)
import Data.Word (Word64)
import qualified StrictList2 as SL


boolField       :: Field Bool   -- Z/2Z, where 1 is True
boolField       = field (Group agFlags (==) (/=) False not id) (&&) True odd id

test1                           :: Int -> (Cmp EV58, Bool) -> IO Bool
-- 1 <= nVars <= 58
test1 nVars (evCmp, isGraded)   = checkGroup ("BinPoly " ++ show nVars) props
  where
    xVarSs          = ['X' : show n | n <- [1 :: Int ..]]
    varSs           = take nVars (map (: []) ['a' .. 'z'] ++ xVarSs)
    (GBPolyOps { evShow, pR, pShow }, BPOtherOps { bpVar, pAt })   =
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
    
    props           = totalOrderProps evSG (==) evCmp
                        ++ withRing pR ringProps pSG pTestEq (eiBit IsCommutativeRing)
                        ++ ringHomomProps pSG pR (===) boolField pToT
                        ++ [readsProp pSG pTestEq
                                (withRing pR polynomReads (zip varSs varPs))]

testBinPoly             :: IO Bool
testBinPoly             =
    checkAll $ checkGroup "boolField" (withRing boolField fieldProps (show, Gen.bool) (===))
        : [test1 nVars evCmp_isGraded
            | nVars <- [1 .. 6] ++ [10, 18 .. 58],
              evCmp_isGraded <- [(lexCmp58, False), (grLexCmp58, True), (grRevLexCmp58, True)]]
