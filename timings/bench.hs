{-# LANGUAGE DataKinds #-}

import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bench, bgroup, defaultMain, whnfIO)

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.GroebnerBasis
import Math.Algebra.Commutative.UPoly
import Math.Algebra.Commutative.EPoly
import Math.Algebra.Commutative.BinPoly
-- import Math.Algebra.Commutative.VMPoly
import qualified Math.Algebra.Linear.SparseVector as SV
import Math.Prob.Random

import Control.DeepSeq (force)
import Control.Monad ((<$!>))
import Data.Bits ((.|.), complement, finiteBitSize, shift, unsafeShiftL, unsafeShiftR)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (transpose)
-- import Data.Poly.Multi (toMultiPoly)
import Data.Strict.Classes (toStrict)
import qualified Data.Strict.Tuple as S
import Data.Tuple.Extra (both)
-- import qualified Data.Vector as PV
-- import qualified Data.Vector.Unboxed as VU
import Data.Word (Word64)
import Fmt ((+|), (|+))
import qualified StrictList2 as SL
import System.Random (mkStdGen, uniformR, split)


main            :: IO ()
main            = defaultMain $ map (uncurry bgroup) [
    ("StrictList", benchesStrictList), ("SparseVector", benchesSV),
    ("UPoly", benchesUPoly), ("EPoly", benchesEPoly), ("BinPoly", benchesBinPoly)
    -- , ("VMPoly", benchesVMPoly)
    {- , @@ other modules -}
    ]


benchWhnf       :: (a -> r) -> (c -> String) -> (c -> a) -> c -> Benchmark
-- Benchmark a function on possibly large arguments, allowing them to be garbage collected
-- outside the run. @c@ should be a smaller type. To force evaluation of @NFData@, apply
-- @(force .)@ to @f@ and/or @argsF@.
benchWhnf f nameF argsF c   =
    withResource (newIORef (argsF c)) (`writeIORef` undefined) $
        (\argsIO -> bench (nameF c) $ whnfIO $ f <$> argsIO) . (id <$!>) . (>>= readIORef)

bench2Whnf      :: (a -> b -> r) -> (c -> String) -> (c -> a) -> (c -> b) -> c -> Benchmark
-- Benchmark a function on 2 possibly large arguments, allowing them to be garbage collected
-- outside the run. @c@ should be a smaller type. To force evaluation of @NFData@, apply
-- @(force .)@ to @f@, @xF@, and/or @yF@.
bench2Whnf f nameF xF yF    = benchWhnf (S.uncurry f) nameF (\c -> xF c S.:!: yF c)


stMap           :: (a -> b) -> SL.List a -> SL.List b
-- @map@ for strict lists using the stack (recursion)
stMap  f (x :! xs)  = f x :! stMap f xs
stMap _f SL.Nil     = SL.Nil

benchesStrictList   :: [Benchmark]
benchesStrictList   =
    concat [forceBenches, sumBenches, lengthBenches, reverseBenches, mapBenches]
  where
    numsSL n        = SL.fromList [0 .. n - 1 :: Int]
    numsLL n        = force [0 .. n - 1 :: Int]
    showSize        :: Text -> Int -> String
    showSize adj n  = ""+|adj|+" "+|n|+""
    forceBenches    = map ($ 1000) [
        benchWhnf force               (showSize "force SL")        numsSL,
        benchWhnf force               (showSize "force LL")        numsLL]
    sumBenches      =  (benchWhnf sum (showSize "sum SL") numsSL <$> [100, 1000])
                    ++ (benchWhnf sum (showSize "sum LL") numsLL <$> [100, 1000])
    lengthBenches   = map ($ 1000) [
        benchWhnf length              (showSize "length SL")       numsSL,
        benchWhnf length              (showSize "length LL")       numsLL]
    reverseBenches  = map ($ 1000) [
        benchWhnf SL.reverse          (showSize "SL.reverse")      numsSL,
        benchWhnf (force . reverse)   (showSize "force . reverse") numsLL]
    mapBenches      = map ($ 1000) [
        benchWhnf (fmap (+ 1))        (showSize "fmap SL")         numsSL,
        benchWhnf (SL.mapReversed (+ 1)) (showSize "SL.mapReversed SL") numsSL,
        benchWhnf (stMap (+ 1))       (showSize "stMap SL")        numsSL,
        benchWhnf (force . map (+ 1)) (showSize "force map")       numsLL]


intRing         :: Ring Int
intRing         = numRing rFlags (const intDiv)
  where
    rFlags  = RingFlags { commutative = True, noZeroDivisors = False, nzInverses = False }
    intDiv y 0      = (0, y)
    intDiv y m      = quotRem y m

divDeep'        :: Ring r -> (r -> r -> S.Pair r r)
divDeep' rR     = toStrict .* rR.bDiv (IsDeep True)

adjNTermsS          :: Text -> Int -> String
-- show an adjective and number of terms
adjNTermsS adj nt   = ""+|nt|+" "+|adj|+" terms"

showNtSparse, showNtDense       :: Int -> String
(showNtSparse, showNtDense)     = both adjNTermsS ("sparse", "dense")

op2SF                   :: (c -> String) -> String -> (c -> String) -> c -> String
op2SF xSF opS ySF c     = xSF c <> opS <> ySF c

benchesSV       :: [Benchmark]
benchesSV       = plusBenches
  where
    UnivL vAG (TgtArrsF iCToV) _univF   = SV.agUniv intRing.ag
    makeSV g (m, n) = sumL' vAG $ take m    -- 11 should not divide n
        [iCToV (r `rem` n) (r `rem` 11 - 5) | r <- randomsBy (uniformR (0, 11 * n - 1)) g]
    (g0, g1)        = split (mkStdGen 37)
    plusBenches     = bench2Whnf vAG.plus (("Add " <>) . show) (makeSV g0) (makeSV g1) <$>
                        [(20, 1000), (300, 1000), (700, 1000),
                         (1000, 100_000), (10_000, 100_000), (30_000, 100_000),
                         (1000, 2 ^ (finiteBitSize (0 :: Int) - 5))]

benchesUPoly    :: [Benchmark]
benchesUPoly    = concat [plusBenches, timesBenches, divBenches]
  where
    UnivL pR _ _    = upUniv intRing
    poly termF nt   = SL.fromListReversed (map termF [0 .. nt - 1])
    sparseTerm m i  = SSTerm (m * i + 1) (fromIntegral (i ^ m))
    denseTerm m i   = SSTerm (i ^ (m :: Int) + 1) (fromIntegral i)
    (smallSparse, bigSparse)    = both (poly . sparseTerm) (2, 3)
    plusBenches     = bench2Whnf pR.plus  (op2SF showNtSparse " + " showNtSparse)
                        smallSparse bigSparse <$> [10, 100, 1000, 10000]
    timesBenches    = bench2Whnf pR.times (op2SF showNtSparse " * " showNtSparse)
                        smallSparse bigSparse <$> [10, 100]
    divBenches      = bench2Whnf (divDeep' pR) divNameF bigDense smallDense <$> [10, 100]
    bigDense        = poly (denseTerm 3) . (2 *)
    smallDense      = poly (denseTerm 2)
    divNameF        = op2SF (showNtDense . (2 *)) " / " showNtDense

benchesEPoly    :: [Benchmark]
benchesEPoly    = concatMap concat . transpose $ map ptdBs [3, 6, 9, 12]
  where
    eLs _ 0         = [[]]
    eLs d nVars     = concat [(e :) <$> eLs d (nVars - 1) | e <- [0 .. d]]
    ptdBs nVars     = [plusBenches, timesBenches, divBenches]
      where
        evCmp           = epEvCmpF nVars GrRevLexCmp
        UnivL pR _ _    = (epOps intRing nVars evCmp).epUniv
        poly m d        = ssFoldSort intRing.ag evCmp
                            [SSTerm (fromIntegral (sum eL) + m) (evMake eL) | eL <- eLs d nVars]
        showSize d      = ""+|nVars|+" vars, "+|showNtDense (fromIntegral (d + 1) ^ nVars)|+""
        plusBenches     = bench2Whnf pR.plus  (op2SF showSize " + " showSize) (poly 2) (poly 3)
                            <$> [1 .. if nVars < 9 then 2 else 1]
        timesBenches    = bench2Whnf pR.times (op2SF showSize " * " showSize) (poly 2) (poly 3)
                            . fromIntegral <$> [1 .. 3 - nVars `quot` 3]
        divBenches      = bench2Whnf (divDeep' pR) divNameF (poly 3 . (+ 1)) (poly 2)
                            <$> [1 .. if nVars < 9 then 1 else 0]
        divNameF        = op2SF (showSize . (+ 1)) " / " showSize

benchesBinPoly  :: [Benchmark]
benchesBinPoly  = concat [plusBenches, timesBenches, divBenches]
  where
    evCmp           = evCmp58 LexCmp
    descVarTs       = replicate 30 "x"
    (GBPolyOps { pR }, _)   = bp58Ops evCmp (secIsGraded LexCmp) descVarTs (UseSugar False)
    binom n k       = foldl' (\res (m, d) -> res * m `quot` d) 1 (zip [n, n - 1 ..] [1 .. k])
        -- assumes 0 <= k and the multiplications don't overflow
    okPops          :: Int -> Int -> Int -> [Word64]
    -- { w | minPop <= popCount w <= maxPop }; 0 <= nVars <= 64,
    -- the result is in ascending lex order.
    okPops minPop maxPop nVars
        | nVars < minPop || maxPop < 0 || maxPop < minPop   = []
        | minPop == 64                                      = [complement 0]
        | otherwise     = go (nVars - minPop) maxPop (1 `shift` (nVars - 1))
      where
        -- go max0s max1s topBit: 0 <= max0s, max1s; topBit < 2^(max0s + max1s)
        go max0s max1s topBit
            | topBit == 0 || max1s == 0     = [0]
            | max0s == 0                    = [(topBit `unsafeShiftL` 1) - 1]
            | otherwise                     = go (max0s - 1) max1s b1 ++
                                                ((topBit .|.) <$> go max0s (max1s - 1) b1)
          where
            b1      = topBit `unsafeShiftR` 1
    poly minPop maxPop nVars    =
        SL.fromListReversed (fromBits58 <$> okPops minPop maxPop nVars)
    showSize minPop maxPop nVars    =
        ""+|nVars|+" vars, "+|showNtDense (sum (binom nVars <$> [minPop .. maxPop]))|+""
    plusBenches     = bench2Whnf pR.plus  (op2SF (showSize 4 4) " + " (showSize 0 4))
                        (poly 4 4) (poly 0 4) <$> [5, 10, 20, 30]
    timesBenches    = bench2Whnf pR.times (op2SF (showSize 4 4) " * " (showSize 0 4))
                        (poly 4 4) (poly 0 4) <$> [5, 10]
    divBenches      = bench2Whnf (divDeep' pR) divNameF (poly 4 4) (poly 2 2)
                        <$> [5, 10, 20, 30]
    divNameF        = op2SF (showSize 4 4) " / " (showSize 2 2)

{-
benchesVMPoly   :: [Benchmark]
benchesVMPoly   = concatMap concat . transpose $ map ptdBs [3, 6, 9, 12]
  where
    eLs             :: Word -> Int -> [[Word]]
    eLs _ 0         = [[]]
    eLs d nVars     = concat [(e :) <$> eLs d (nVars - 1) | e <- [0 .. d]]
    ptdBs nVars     = case someNatVal (fromIntegral nVars + 1) of
     SomeNat (Proxy :: Proxy n1)    -> [plusBenches, timesBenches, divBenches]
      where
        GBPolyOps { pR }    = vmpModPwGbpOps @2_000_003 @n1 @('IsGraded 'True) (UseSugar True)
        fromExps es     = (vmpEvFromExps es :: VMPolyEV n1 ('IsGraded 'True)).ev
        poly m d        =
            force $ VMPolyModPw $ toMultiPoly {- sorts and filters -} $ PV.fromList
                [(fromExps $ VU.fromList eL, fromInteger $ fromIntegral (sum eL) + m)
                    | eL <- eLs d nVars]
        showSize d      = ""+|nVars|+" vars, "+|showNtDense (fromIntegral (d + 1) ^ nVars)|+""
        plusBenches     = bench2Whnf (force . pR.plus)  (op2SF showSize " + " showSize)
                            (poly 2) (poly 3) <$> [1 .. if nVars < 9 then 2 else 1]
        timesBenches    = bench2Whnf (force . pR.times) (op2SF showSize " * " showSize)
                            (poly 2) (poly 3) . fromIntegral <$> [1 .. 3 - nVars `quot` 3]
        divBenches      = bench2Whnf (force . divDeep' pR) divNameF (poly 3 . (+ 1)) (poly 2)
                            <$> [1 .. if nVars < 9 then 1 else 0]
        divNameF        = op2SF (showSize . (+ 1)) " / " showSize
-}
