{-# LANGUAGE NoMonomorphismRestriction #-}

import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bench, bgroup, defaultMain, whnf, whnfIO)

import Math.Algebra.General.Algebra
import Math.Algebra.Category.Category
import Math.Algebra.Commutative.Field.ZModPW
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
import Data.Bifunctor (first)
import Data.Bits ((.|.), complement, finiteBitSize, shift, unsafeShiftL, unsafeShiftR)
import qualified Data.IntMap.Strict as IM
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (transpose)
-- import Data.Mod.Word (Mod)
-- import Data.Poly.Multi (toMultiPoly)
import Data.Strict.Classes (toLazy, toStrict)
import qualified Data.Strict.Tuple as S
import Data.Tuple.Extra (both)
-- import qualified Data.Vector as PV
-- import qualified Data.Vector.Unboxed as VU
import Data.Word (Word64)
import Fmt ((+|), (|+))
import qualified StrictList2 as SL
import StrictList2 (StrictList)
import System.Random (mkStdGen, uniformR)


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


stMap           :: (a -> b) -> StrictList a -> StrictList b
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


divDeep'        :: Ring r -> (r -> r -> S.Pair r r)
divDeep' rR     = toStrict .* rR.bDiv (IsDeep True)

adjNTermsS          :: Text -> Int -> String
-- show an adjective and number of terms
adjNTermsS adj nt   = ""+|nt|+" "+|adj|+" terms"

showNtSparse, showNtDense       :: Int -> String
(showNtSparse, showNtDense)     = both adjNTermsS ("sparse", "dense")

op2SF                   :: (c -> String) -> String -> (c -> String) -> c -> String
op2SF xSF opS ySF c     = xSF c <> opS <> ySF c

type ModP       = ModWord32 2_000_003
type SVU        = SV.VectorU ModP
type SVZ        = SV.Vector Integer
-- type IMV        = IM.IntMap ModP    -- only nonzero terms

benchesSV       :: [Benchmark]
benchesSV       = picBenches <> sizeBenches <> plusBenches <> scaleBenches <> permuteBenches
  where
    vuAG            = SV.mkAGU      :: AbelianGroup SVU
    vzAG            = SV.mkAG zzAG  :: AbelianGroup SVZ
    plusIM1 x y     = IM.filter (/= 0) (IM.unionWith (+) x y)
    maybePlus _ a b     = let c = a + b in if c == 0 then Nothing else Just c
    plusIM2         = IM.mergeWithKey maybePlus id id
    scaleIMNzd c    = IM.map (c *)

    icIsNz          = (/= 0) . S.snd
    fromInt i       = fromInteger . fromIntegral $ (i :: Int)
    makeSV g (m, n) =   -- at most m terms in dim n
        SV.random icIsNz n m (first fromInt . uniformR (-5, 5)) g
    makeSVU         = makeSV :: _ -> _ -> SVU
    makeSVZ         = makeSV :: _ -> _ -> SVZ
    showMN (m, n)   = "≤"+|m|+" terms in dim "+|n|+""
    someMNs         = ((, 1000) <$> [20, 300, 700]) ++
                        ((, 100_000) <$> [1000, 10_000, 30_000]) ++
                        [(1000, 2 ^ (finiteBitSize (0 :: Int) - 5))]
    (g0, g1)        = splitGen (mkStdGen 37)
    iToVUs i        = sum [SV.index 0 (SV.fromNzIC i (fromInt n) :: SVU) i | n <- [1 .. 1000]]
    iToVZs i        = sum [SV.index 0 (SV.fromNzIC i (fromInt n) :: SVZ) i | n <- [1 .. 1000]]
    
    vToIM           = IM.fromDistinctAscList . map toLazy . SV.toDistinctAscNzs
    makeIM          = vToIM .* makeSVU

    picBenches      = (benchWhnf iToVUs (("index . iCToVU, x1000 / ind " <>) . show) id <$>
                        [10 ^ n | n <- [0 :: Int, 2, 4, 6, 12, 18]])
                ++    (benchWhnf iToVZs (("index . iCToVZ, x1000 / ind " <>) . show) id <$>
                        [10 ^ n | n <- [0 :: Int, 2, 4, 6, 12, 18]])
    sizeBenches     = benchWhnf @SVU SV.size (("sizeU / " <>) . showMN) (makeSV g1) <$> someMNs
    plusBenches     =
        (bench2Whnf vuAG.plus (("AddU / " <>) . showMN) (makeSVU g0) (makeSVU g1) <$> someMNs)
     ++ (bench2Whnf vzAG.plus (("AddZ / " <>) . showMN) (makeSVZ g0) (makeSVZ g1) <$> someMNs)
     ++ (bench2Whnf plusIM1 (("AddIM1 / " <>) . showMN) (makeIM  g0) (makeIM  g1) <$> someMNs)
     ++ (bench2Whnf plusIM2 (("AddIM2 / " <>) . showMN) (makeIM  g0) (makeIM  g1) <$> someMNs)
    scaleBenches    =
        (bench2Whnf SV.timesNzdCU         (("ScaleU / " <>) . showMN) (const 23) (makeSVU g1)
            <$> someMNs)
     ++ (bench2Whnf (SV.timesNzdC zzRing) (("ScaleZ / " <>) . showMN) (const 23) (makeSVZ g1)
            <$> someMNs)
     ++ (bench2Whnf scaleIMNzd           (("ScaleIM / " <>) . showMN) (const 23) (makeIM  g1)
            <$> someMNs)
    
    pKMaxs          = [2, 10, 100, 1000]   :: [Int]
    pRand1000 kMax g    = if kMax == 2 then SV.pCycle (randomIndsDistinct 1000 2 g) else
        SV.pRandom 1000 kMax g
    perm0s          = map (`pRand1000` g0) pKMaxs
    perm1s          = map (`pRand1000` g1) pKMaxs
    permuteBenches  = concat (zipWith f pKMaxs perm0s)
      where
        f kMax0 p0      = concat (zipWith g pKMaxs perm1s)
          where
            g kMax1 p1      =
                [bench ("Permute.Compose ≤"+|kMax0|+","+|kMax1|+" of 1000 moved")
                        (whnf (SV.pCompose p0) p1)
                    | kMax0 + kMax1 > 15]

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
