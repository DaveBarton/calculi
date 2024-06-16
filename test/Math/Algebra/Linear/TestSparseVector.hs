{- |  This module helps test the "Math.Algebra.Linear.SparseVector" module and its clients.
    
    This module is normally imported qualified.  -}

module Math.Algebra.Linear.TestSparseVector (
    testOps, tests
) where

import Math.Algebra.General.Algebra hiding (assert)
import qualified Math.Algebra.Linear.SparseVector as SV

import Math.Algebra.General.TestAlgebra

import Hedgehog ((===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range


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

tests           :: TestTree
-- ^ Test the "Math.Algebra.Linear.SparseVector" module.
tests           = testGroup "SparseVector" testsL
  where
    cAG             = zzAG
    iTA             = numVarTestOps "e" (Range.exponential 0 1_000_000)
    vTA             = testOps cAG (Range.linear 0 20) iTA (zzTestOps { gen = zzExpGen 200 })
    vAG             = SV.mkAG cAG
    vToU            :: SV.Vector Integer -> Int
    vToU            = SV.foldBIMap' (+) 0 (\i c -> (i `rem` 101 + 5) * fromIntegral c)
    
    testsL          = [abelianGroupTests vTA (IsNontrivial True) vAG,
                        singleTest "homomorphism" $ homomTM vTA vAG.plus (===) (+) vToU]
