{-# LANGUAGE Strict #-}

{- |  This module defines functions for computing and using a Groebner Basis.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.GroebnerBasis (
    gbTSummary, gbTProgressChars, gbTProgressInfo, gbTResults, gbTQueues, gbTProgressDetails,
    groebnerBasis
) where

import Math.Algebra.General.Algebra
import Math.Algebra.General.SparseSum
import Math.Algebra.Commutative.EPoly

import Control.Monad (forM, unless, when)
import Control.Monad.Extra (orM, whileM)
import Data.Array.IArray (Array, (!), listArray)
import Data.Foldable (find, foldl', minimumBy, toList)
import Data.List (elemIndex, findIndices, groupBy, sortBy)
import Data.List.Extra (chunksOf)
import Data.Maybe (catMaybes, fromJust, isJust, isNothing, listToMaybe, mapMaybe)
import qualified Data.Sequence as Seq
import Data.Tuple.Extra (dupe, first, fst3, second)
import GHC.IsList (fromList)
import Numeric (showFFloat)
import qualified StrictList as SL

import Control.Concurrent (ThreadId, forkOn, killThread, myThreadId, threadCapability)
import Control.Concurrent.STM.TVar (TVar, modifyTVar', newTVarIO, readTVar, readTVarIO)
import Control.Monad.STM (atomically, retry)
-- @@@ import Data.Atomics (atomicModifyIORefCAS, atomicModifyIORefCAS_)
-- @@@ import Data.Atomics.Counter (incrCounter_, newCounter, readCounter)
import Data.IORef (IORef, atomicModifyIORef {- @@@ -}, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.IORef.Extra (atomicModifyIORef'_, atomicWriteIORef')

import Data.Time.Clock.System (SystemTime(..), getSystemTime)
import Debug.Trace  -- @@@
import System.CPUTime (getCPUTime)
import System.IO (hPutStr, stderr)
-- import System.IO (hFlush, stdout)
-- import System.Process (callCommand)


slHeadMaybe         :: SL.List a -> Maybe a
slHeadMaybe         = SL.head

slSingleton         :: a -> SL.List a
slSingleton e       = SL.Cons e SL.Nil

{- currently unused
slZipWithReversed   :: (a -> b -> c) -> SL.List a -> SL.List b -> SL.List c
slZipWithReversed f = go SL.Nil
  where
    go cs (SL.Cons a as) (SL.Cons b bs)     = go (f a b `SL.Cons` cs) as bs
    go cs _              _                  = cs
-}

slMergeBy           :: Cmp a -> Op2 (SL.List a)
-- like 'mergeBy' in Data.List.Extra
slMergeBy cmp       = go SL.Nil
  where
    go r xs@(SL.Cons x ~t) ys@(SL.Cons y ~u)    =
        if cmp x y /= GT
        then go (SL.Cons x r) t ys
        else go (SL.Cons y r) xs u
    go r xs                SL.Nil               = SL.prependReversed r xs
    go r SL.Nil            ys                   = SL.prependReversed r ys

-- @@@ change next few to constant stack space?:

slMinusSorted       :: Cmp a -> Op2 (SL.List a)
-- difference of two sorted lists, like 'minusBy' from data-ordlist
slMinusSorted cmp   = go
  where
    go xs@(SL.Cons x ~t) ys@(SL.Cons y ~u)  =
        case cmp x y of
           LT   -> x `SL.Cons` go t ys
           EQ   ->             go t u
           GT   ->             go xs u
    go xs                SL.Nil             = xs
    go SL.Nil            _ys                = SL.Nil

slInsertBy          :: Cmp a -> a -> Op1 (SL.List a)
slInsertBy cmp x    = go
  where
    go ys@(SL.Cons h ~t)    = case cmp x h of
        GT  -> SL.Cons h (go t)
        _   -> SL.Cons x ys
    go SL.Nil               = slSingleton x

slDeleteBy          :: EqRel a -> a -> Op1 (SL.List a)
slDeleteBy eq x     = go
  where
    go ys@(SL.Cons h ~t)    = if x `eq` h then ys else SL.Cons h (go t)
    go SL.Nil               = SL.Nil

evElts          :: [a] -> ()
-- force all elements of a list
evElts          = foldr seq ()

evList          :: [a] -> [a]
-- force all elements of a list, and return it
evList xs       = evElts xs `seq` xs

minIndexBy                      :: Cmp a -> Seq.Seq a -> Int
-- The index of the first least element of a nonempty sequence.
minIndexBy cmp (h Seq.:<| t)    = fst (Seq.foldlWithIndex f (0, h) t)
  where
    f im@(_, m) j e     = if cmp m e == GT then (j, e) else im
minIndexBy _   Seq.Empty        = undefined

inc             :: IORef Int -> Int -> IO ()
inc ref n       = when (n /= 0) $ atomicModifyIORef'_ ref (+ n)

inc1TVar        :: TVar Int -> IO ()
inc1TVar var    = atomically $ modifyTVar' var (+ 1)

{- currently unused
pop             :: IORef [a] -> IO (Maybe a)
pop esRef       = atomicModifyIORef' esRef f
  where
    f (h : t)       = (t, Just h)
    f []            = ([], Nothing)
-}

slPop           :: IORef (SL.List a) -> IO (Maybe a)
slPop esRef     = atomicModifyIORef' esRef f
  where
    f (SL.Cons h t)     = (t, Just h)
    f SL.Nil            = (SL.Nil, Nothing)

maybeAtomicModifyIORef'             :: IORef a -> Pred a -> (a -> (a, b)) -> IO (Maybe b)
-- for speed, trying to avoid atomicModifyIORef'
maybeAtomicModifyIORef' ref p f     = do
    a0      <- readIORef ref
    if not (p a0) then pure Nothing else atomicModifyIORef' ref f'
  where
    f' a    = if not (p a) then (a, Nothing) else second Just (f a)

maybeAtomicModifyIORef              :: IORef a -> Pred a -> (a -> (a, b)) -> IO (Maybe b)
-- for speed, trying to avoid atomicModifyIORef
maybeAtomicModifyIORef ref p f      = do
    a0      <- readIORef ref
    if not (p a0) then pure Nothing else atomicModifyIORef {- @@@ didn't have ' -} ref f'
  where
    f' a    = if not (p a) then (a, Nothing) else second Just (f a)

maybeDequeueRefSeq          :: IORef (Seq.Seq a) -> Pred a -> IO (Maybe a)
maybeDequeueRefSeq ref p    = maybeAtomicModifyIORef' ref p' f
  where
    p' (h Seq.:<| _t)   = p h
    p' _                = False
    f (h Seq.:<| t)     = (t, h)
    f _                 = undefined

elapsedMicroSecs    :: SystemTime -> IO Integer
elapsedMicroSecs (MkSystemTime s0 ns0)      = do
    MkSystemTime s ns       <- getSystemTime
    pure $ 1_000_000 * fromIntegral (s - s0)
        + fromIntegral ns `quot` 1000 - fromIntegral ns0 `quot` 1000

cpuElapsedStr                       :: Integer -> SystemTime -> IO String
cpuElapsedStr cpuTime0 sysTime0     = do
    t       <- getCPUTime
    t1      <- elapsedMicroSecs sysTime0
    pure (showMicroSecs (quot (t - cpuTime0) 1_000_000) ++ "/" ++ showMicroSecs t1)
  where
    showMicroSecs n     = showFFloat (Just 6) (1e-6 * fromIntegral n :: Double) "s"


{- See Gebauer & Moller, J. Symbolic Computation (1988) 6, 275-286;
    Giovini, Mora, Niesi, Robbiano, Traverso, "One sugar cube, please ...", 1991: -}

data SPair          = SPair { _spI, _spJ :: Int, spH :: Word, spLcm :: ExponVec }
    -- i, j, "sugar" (homog) degree, LCM of head evs of gens i and j

spCmp               :: Cmp ExponVec -> Bool -> Cmp SPair
                        -- stable sorts/merges (usually) means j then i breaks ties
spCmp evCmp useSugar (SPair _ _ h1 ev1) (SPair _ _ h2 ev2)  =
    if useSugar then compare h1 h2 <> evCmp ev1 ev2 else evCmp ev1 ev2

type SSPairs        = SL.List SPair     -- Sorted SPairs using (spCmp evCmp True)

data EPolyHDeg c    = EPolyHDeg { phP :: EPoly c, phH :: Word } -- poly and "sugar" homog degree

data GBGenInfo      = GBGenInfo { giEv :: ExponVec, giDh :: Word }

giNew               :: EPolyHDeg c -> GBGenInfo
giNew (EPolyHDeg p h)   =   -- p /= 0, h is "sugar" (homog) degree
    let ev      = ssDegNZ p
    in  GBGenInfo ev (h - totDeg ev)

giLcm               :: Int -> Op2 GBGenInfo
giLcm nVars gi1 gi2 = GBGenInfo (evLCM nVars (giEv gi1) (giEv gi2)) (max (giDh gi1) (giDh gi2))

giToSp              :: Int -> Int -> GBGenInfo -> SPair
giToSp i j gi       =
    let ev      = giEv gi
    in  SPair i j (giDh gi + totDeg ev) ev

{-# SCC updatePairs #-}
updatePairs         :: Int -> Cmp ExponVec -> [Maybe GBGenInfo] -> SSPairs -> GBGenInfo ->
                        ([Int], SSPairs, SSPairs)
updatePairs nVars evCmp gMGis ijcs tGi      = (skipIs, skipIJCs, addITCs)
  where
    evDivs          = evDivides nVars
    hEvCmp          = spCmp evCmp True          :: Cmp SPair
    lcmCmp          = spCmp evCmp False         :: Cmp SPair
    hCmp            = compare `on` spH          :: Cmp SPair
    t               = length gMGis
    tEv             = giEv tGi
    itMGis          = map (fmap (giLcm nVars tGi)) gMGis    :: [Maybe GBGenInfo]
    itmcs           = map (fmap giEv) itMGis                :: [Maybe ExponVec]     -- lcms
    itmcsA          = listArray (0, t - 1) itmcs            :: Array Int (Maybe ExponVec)
    divEq ev c      = assert (evDivs ev c) (totDeg ev == totDeg c)
    skipIQs         = zipWith skipQ gMGis itmcs     -- newly redundant gens
      where
        skipQ (Just gi) (Just c)    = divEq (giEv gi) c
        skipQ _         _           = False
    skipIs          = evList (findIndices id skipIQs)
    ijcs0           = if null skipIs then SL.Nil else   -- for efficiency
                      SL.filter (\(SPair i j _ _) -> i `elem` skipIs || j `elem` skipIs) ijcs
    ijcs1           = SL.filter (\(SPair i j _ c) -> evDivs tEv c && ne i c && ne j c) ijcs
      where             -- criterion B_ijk
        ne i c      = maybe False (\itc -> not (divEq itc c)) (itmcsA ! i)
    skipIJCs        = slMergeBy hEvCmp ijcs0 ijcs1  -- @@@ was evList
    itcs            = catMaybes (zipWith (\i -> fmap (giToSp i t)) [0..] itMGis)    :: [SPair]
    -- "sloppy" sugar method:
    itcss           = groupBy (cmpEq lcmCmp) (sortBy lcmCmp itcs)
    itcsToC         = spLcm . head
    itcss'          = filter (noDivs . itcsToC) itcss       -- criterion M_ik
      where
        firstDiv c  = find (\ itcs1 -> evDivs (itcsToC itcs1) c) itcss
        noDivs c    = divEq (itcsToC (fromJust (firstDiv c))) c
    gMEvsA          = listArray (0, t - 1) (map (fmap giEv) gMGis)
                        :: Array Int (Maybe ExponVec)
    bestH           = minimumBy hCmp
    itcs'           = mapMaybe (\gp -> if any buch2 gp then Nothing else Just (bestH gp)) itcss'
      where             -- criterion F_jk and Buchberger's 2nd criterion (gi and gt rel. prime)
        buch2 (SPair i j _ c)     = assert (j == t)
            (totDeg (fromJust (gMEvsA ! i)) + totDeg tEv == totDeg c)
    addITCs         = fromList (sortBy hEvCmp itcs')    -- @@@ was evList


data SizedEPoly c   = SizedEPoly { sepN :: Int, sepP :: EPoly c }

sizeEP              :: EPoly c -> SizedEPoly c
sizeEP p            = SizedEPoly (ssNumTerms p) p

data ENPs c         = ENPs { _enpsE :: Word, _enpsL :: SL.List (SizedEPoly c) }
-- exponent and list of ps

-- nVars > 0, each enpss has increasing es, all p /= 0, (ssDegNZ p) unique:
type KerGens c      = Seq.Seq (SL.List (ENPs c))

data GapKerGens c   = G1KGs { g1kgsGap :: Word, _g1kgsKgs :: KerGens c }

type GapsKerGens c  = SL.List (GapKerGens c)    -- gaps increasing, 0 gap always present

kgsNew              :: Int -> KerGens c
kgsNew nVars        = Seq.replicate nVars SL.Nil

gkgsNew             :: Int -> GapsKerGens c
gkgsNew nVars       = slSingleton (G1KGs 0 (kgsNew nVars))

kgsSepCmp           :: Cmp (SizedEPoly c)
kgsSepCmp (SizedEPoly n1 p1) (SizedEPoly n2 p2)   =
    n1 `compare` n2 <> gRevLex (ssDegNZ p1) (ssDegNZ p2)

kgsInsert           :: forall c. EPoly c -> Op1 (KerGens c)
kgsInsert p kgs     =       -- p /= 0, nVars > 0
    assert (not (ssIsZero p) && Seq.length kgs > 0) $
    let nVars   = Seq.length kgs
        es      = exponsL nVars (ssDegNZ p)
        m       = maximum es
        v       = fromJust (elemIndex m es)
        np      = sizeEP p
        ins             :: Op1 (SL.List (ENPs c))
        ins SL.Nil      = slSingleton (ENPs m (slSingleton np))
        ins enpss@(SL.Cons enps@(ENPs e ~nps) ~t)
            | m < e     = SL.Cons (ENPs m (slSingleton np)) enpss
            | m == e    = SL.Cons (ENPs m (slInsertBy kgsSepCmp np nps)) t
            | otherwise = SL.Cons enps (ins t)
    in  Seq.adjust' ins v kgs

gkgsInsert          :: forall c. EPolyHDeg c -> Op1 (GapsKerGens c)
gkgsInsert (EPolyHDeg p hDeg)     = go    -- p /= 0, nVars > 0
  where
    gap                     = hDeg - totDeg (ssDegNZ p)
    go (SL.Cons h@(G1KGs gap0 kgs0) t)  = assert (gap >= gap0) $
        if gap == gap0 then SL.Cons (G1KGs gap (kgsInsert p kgs0)) t
        else if maybe True ((gap <) . g1kgsGap) (slHeadMaybe t) then
            SL.Cons h (SL.Cons (G1KGs gap (kgsInsert p (kgsNew (Seq.length kgs0)))) t)
        else SL.Cons h (go t)
    go SL.Nil                           = undefined

kgsDelete           :: forall c. EPoly c -> Op1 (KerGens c)
kgsDelete p kgs     =       -- p in kgs (so p /= 0, nVars > 0), (ssDegNZ p) unique in kgs
    assert (not (ssIsZero p) && Seq.length kgs > 0) $
    let nVars   = Seq.length kgs
        es      = exponsL nVars (ssDegNZ p)
        m       = maximum es
        v       = fromJust (elemIndex m es)
        np      = sizeEP p
        eq np1 np2      = kgsSepCmp np1 np2 == EQ
        del             :: Op1 (SL.List (ENPs c))
        del (SL.Cons enps@(ENPs e ~nps) t)
            | m > e     = SL.Cons enps (del t)
            | m == e    = assert (isJust (find (eq np) nps)) $
                            SL.Cons (ENPs m (slDeleteBy eq np nps)) t
            | otherwise = undefined
        del SL.Nil      = undefined
    in  Seq.adjust' del v kgs

gkgsDelete          :: forall c. EPolyHDeg c -> Op1 (GapsKerGens c)
gkgsDelete (EPolyHDeg p hDeg)     = go      -- p in gkgs (so p /= 0, nVars > 0),
                                            -- (ssDegNZ p) unique in gkgs
  where
    gap                     = hDeg - totDeg (ssDegNZ p)
    go (SL.Cons h@(G1KGs gap0 kgs0) t)  = assert (gap >= gap0) $
        if gap == gap0 then SL.Cons (G1KGs gap (kgsDelete p kgs0)) t
        else SL.Cons h (go t)
    go SL.Nil               = undefined

-- kgsReplace              :: EPoly c -> EPoly c -> Op1 (KerGens c)
-- kgsReplace p p' kgs     = kgsInsert p' (kgsDelete p kgs)

gkgsReplace             :: EPolyHDeg c -> EPolyHDeg c -> Op1 (GapsKerGens c)
gkgsReplace ph ph' gkgs = gkgsInsert ph' (gkgsDelete ph gkgs)

{-# SCC kgsFindReducer #-}
kgsFindReducer          :: forall c. EPoly c -> KerGens c -> Maybe (EPoly c)
-- returns the best (shortest) top-reducer, if any
kgsFindReducer p kgs    =
    if ssIsZero p then Nothing else
    let nVars   = Seq.length kgs
        pEv     = ssDegNZ p
        npsF bnp                   SL.Nil                               = bnp
        npsF bnp@(SizedEPoly bn _) (SL.Cons ng@(SizedEPoly n ~g) ~t)
            | bn <= n   = bnp
            | otherwise = npsF (if evDivides nVars (ssDegNZ g) pEv then ng else bnp) t
        esF bnp _  SL.Nil   = bnp
        esF bnp pe (SL.Cons (ENPs e ~nps) ~t)
            | pe < e    = bnp
            | otherwise = esF (npsF bnp nps) pe t
        vF bnp (pe, enpss)      = esF bnp pe enpss
        resSep  = foldl' vF (SizedEPoly (maxBound :: Int) SSZero)
                    (zip (exponsL nVars pEv) (toList kgs))
    in  if sepN resSep < (maxBound :: Int) then Just (sepP resSep) else Nothing

gkgsFindReducer         :: forall c. EPoly c -> GapsKerGens c -> Maybe (EPolyHDeg c)
-- returns the best (least sugar gap, then shortest) top-reducer, if any
gkgsFindReducer p gkgs  = listToMaybe (mapMaybe find1 (toList gkgs))
  where
    find1 (G1KGs gap kgs)   =
        fmap (\g -> EPolyHDeg g (totDeg (ssDegNZ g) + gap)) (kgsFindReducer p kgs)

sugarReduce             :: (EPoly c -> EPoly c -> (EPoly c, EPoly c)) ->
                            EPolyHDeg c -> EPolyHDeg c -> (EPolyHDeg c, Int)
sugarReduce div2 (EPolyHDeg p pHDeg) (EPolyHDeg g gHDeg)    = (EPolyHDeg r rHDeg, nSteps)
  where
    (q, r)      = div2 p g
    rHDeg       = if ssIsZero q then pHDeg else max pHDeg (epHomogDeg0 q + gHDeg)
    nSteps      = ssNumTerms q

gkgsTopReduce           :: (EPoly c -> EPoly c -> (EPoly c, EPoly c)) -> IO (GapsKerGens c, Int)
                            -> IORef Int -> EPolyHDeg c -> IO (EPolyHDeg c, Int)
-- top-reduce a (gh, kN)
gkgsTopReduce div2 kerVar nRedStepsRef      = go
  where
    go ph@(EPolyHDeg p _)    = do
        (ker, nGens)    <- kerVar
        let go1 gh      = do
                let (rh, nSteps)    = sugarReduce div2 ph gh
                -- @@@ inc nRedStepsRef nSteps
                go rh
        maybe (pure (ph, nGens)) go1 (gkgsFindReducer p ker)

kgsReduce               :: (EPoly c -> EPoly c -> (EPoly c, EPoly c)) -> KerGens c -> EPoly c ->
                            (EPoly c, Int)
-- fully reduce a polynomial, counting steps
kgsReduce div2 kgs      = go 0
  where
    go nRedSteps p  = if ssIsZero p then (SSZero, nRedSteps) else
                        maybe go2 go1 (kgsFindReducer p kgs)
      where
        go1 g   =
            let (q, r)      = div2 p g
            in  go (nRedSteps + ssNumTerms q) r
        ~go2    =
            let SSNZ c d t          = p
                (t', nRedSteps')    = go nRedSteps t
            in  (SSNZ c d t', nRedSteps')

foldReduce                  :: forall c f. Foldable f => Int ->
                                (EPoly c -> EPoly c -> (EPoly c, EPoly c)) -> f (EPoly c) ->
                                EPoly c -> (Bool, EPoly c, Int)
-- fully reduce by folding (not kgs), except stop and return True if/when a deg > 0 quotient
foldReduce nVars div2 g0s   = go 0      -- all g0s /= 0, with gap 0
  where
    go nRedSteps p      = if ssIsZero p then (False, SSZero, nRedSteps) else
        let pEv     = ssDegNZ p
            mg      = find (\g -> evDivides nVars (ssDegNZ g) pEv) g0s
            useG g  =
                let (q, r)      = div2 p g
                in  if totDeg (ssDegNZ q) > 0 then (True, r, nRedSteps + ssNumTerms q)
                    else go (nRedSteps + 1) r
            ~go2    =
                let SSNZ c d t              = p
                    (todo, t', nRedSteps')  = go nRedSteps t
                in  (todo, SSNZ c d t', nRedSteps')
        in  maybe go2 useG mg

foldTopReduce1              :: forall c f. Foldable f => Int ->
                                (EPoly c -> EPoly c -> (EPoly c, EPoly c)) -> f (EPolyHDeg c) ->
                                EPolyHDeg c -> Maybe (EPolyHDeg c, Int)
-- do 1 folding step if there's a top-reducer
foldTopReduce1 nVars div2 ghs ph@(EPolyHDeg p _)    =       -- all gs /= 0
    if ssIsZero p then Nothing else
    let pEv     = ssDegNZ p
        mgh     = find (\gh -> evDivides nVars (ssDegNZ (phP gh)) pEv) ghs
            -- @@@ improve to find best reducer!?
    in  fmap (sugarReduce div2 ph) mgh


-- | gbTrace bits for 'groebnerBasis' tracing. Bits 0x0F are useful to end users.
gbTSummary, gbTProgressChars, gbTProgressInfo, gbTResults, gbTQueues, gbTProgressDetails  :: Int
gbTSummary          = 0x01  -- ^ a short summary at the end of a run
gbTProgressChars    = 0x02  -- ^ total degree for each s-poly reduction result
gbTProgressInfo     = 0x04  -- ^ info when adding or removing a generator
gbTResults          = 0x08  -- ^ output final generators
gbTQueues           = 0x10  -- ^ info about threads and their queues ("cdprRsS", "rg")
gbTProgressDetails  = 0x20  -- ^ details relating to selection strategy

printThreadCapabilities     :: String -> [ThreadId] -> IO ()
printThreadCapabilities prefix otherThreadIds   = do
    firstThreadId       <- myThreadId
    capInfos            <- mapM threadCapability (firstThreadId : otherThreadIds)
    putStr $ prefix ++ "Threads are on capabilities: "
    mapM_ (putStrLn . unwords) (chunksOf 20 (map (show . fst) capInfos))

groebnerBasis       :: forall c. Int -> Cmp ExponVec -> Field c -> Ring (EPoly c) -> [EPoly c]
                        -> Int -> Int -> (EPoly c -> String) -> IO [EPoly c]
groebnerBasis nVars evCmp cField epRing initGens nCores gbTrace epShow    = do
    cpuTime0        <- getCPUTime
    sysTime0        <- getSystemTime
    cpuTime1Ref     <- newIORef cpuTime0
    gkgsRef         <- newIORef (gkgsNew nVars, 0)  -- (gkgs, # gens)
    nRedStepsRef    <- newIORef 0           :: IO (IORef Int)
    nSPairsRedRef   <- newIORef 0           :: IO (IORef Int)
    let gbTQueues1  = gbTrace .&. gbTQueues /= 0 && nCores > 1
        topDiv2     = rBDiv2 epRing False
        topReduce   = gkgsTopReduce topDiv2 (readIORef gkgsRef) nRedStepsRef
        reduce2 SSZero          = pure SSZero
        reduce2 (SSNZ c d t)    = do
            (SL.Cons (G1KGs 0 kgs) _, _)    <- readIORef gkgsRef
            let (t', nSteps)        = kgsReduce topDiv2 kgs t
            -- @@@ inc nRedStepsRef nSteps
            pure (SSNZ c d t')
        reduce_n gh = do
            (EPolyHDeg g1 h1, n)    <- topReduce gh
            g2                      <- reduce2 (ssForceTails g1)
            pure (EPolyHDeg g2 h1, n)
    genHsRef        <- newIORef Seq.empty   :: IO (IORef (Seq.Seq (EPolyHDeg c)))
    let gap0NZ (EPolyHDeg g h)  = if h /= totDeg (ssDegNZ g) then Nothing else Just g
        endReduce_n kN gh       = do
            ghs         <- readIORef genHsRef
            let kN'     = Seq.length ghs
            if kN == kN' || ssIsZero (phP gh) then pure (gh, kN')
            else if 3 * nVars * (kN' - kN) > kN' {- @@ tune -} then reduce_n gh
            else
                let endGHs      = Seq.drop kN ghs
                    mghn        = foldTopReduce1 nVars topDiv2 endGHs gh
                    endRed1 (ph, nSteps)    = do
                        -- @@@ inc nRedStepsRef nSteps
                        reduce_n ph
                    endRed2 (EPolyHDeg (SSNZ c d t) h)  = do
                        let g0s                 = mapMaybe gap0NZ (toList endGHs)
                            (todo, t', nSteps)  = foldReduce nVars topDiv2 g0s t
                        -- @@@ inc nRedStepsRef nSteps
                        p       <- (if todo then reduce2 else pure) (SSNZ c d t')
                        pure (EPolyHDeg p h, kN')
                    endRed2 (EPolyHDeg SSZero _)        = undefined
                in  maybe (endRed2 gh) endRed1 mghn
    -- rgs is a [(g, i)] of nonzero g with descending (ssDegNZ g)
    rNTraceRef      <- newIORef 0
    let rgsInsert   :: EPolyHDeg c -> Int -> [(EPoly c, Int)] -> IO [(EPoly c, Int)]
        rgsInsert (EPolyHDeg g _) i []                  = pure [(g, i)]
        rgsInsert gh@(EPolyHDeg g gHDeg) i rgs@((h, j) : t)
            | evCmp (ssDegNZ g) (ssDegNZ h) == GT       = pure ((g, i) : rgs)
            | evDivides nVars (ssDegNZ g) (ssDegNZ h)   = do
                when (gbTrace .&. gbTProgressInfo /= 0) $
                    putStrLn $ " remove g" ++ show j ++ " (" ++ _showEV h ++ ") by g" ++ show i
                        ++ " (" ++ _showEV g ++ ")"
                ghs     <- readIORef genHsRef
                let hh  = Seq.index ghs j
                atomicModifyIORef'_ gkgsRef (first (gkgsDelete hh))
                rgsInsert gh i t
            | otherwise                                 = do
                t'          <- rgsInsert gh i t
                if gHDeg /= totDeg (ssDegNZ g) then pure ((h, j) : t') else do
                    let (q, r)  = rBDiv2 epRing True h g
                    if ssIsZero q then pure ((h, j) : t') else do
                        -- @@@ inc nRedStepsRef (ssNumTerms q)
                        when (gbTrace .&. gbTQueues /= 0) $
                            if totDeg (ssDegNZ q) == 0 then inc rNTraceRef 1 else putChar 'R'
                        r'          <- if totDeg (ssDegNZ q) == 0 then pure r else reduce2 r
                        ghs0        <- readIORef genHsRef
                        let hh      = Seq.index ghs0 j
                            rh'     = EPolyHDeg r' (phH hh)
                        atomicModifyIORef'_ gkgsRef (first (gkgsReplace hh rh'))
                        atomicModifyIORef'_ genHsRef (Seq.update j rh')
                        assert (not (ssIsZero r')) (pure ((r', j) : t'))
    wakeAllThreads  <- newTVarIO 0          :: IO (TVar Int)
    wakeMainThread  <- newTVarIO 0          :: IO (TVar Int)
    gDShownRef      <- newIORef 0           :: IO (IORef Integer)
    let putS        = if gbTrace .&. gbTProgressChars /= 0 then hPutStr stderr else putStr
    let addGenHN (gh, kN)   = {-# SCC addGenHN #-} do
            (EPolyHDeg g0 h, _)     <- endReduce_n kN gh
            unless (ssIsZero g0) $ do
                let g1      = traceEvent "  addGenHN start" $ withRing cField ssMonicize g0
                    gh1     = EPolyHDeg g1 h
                    f (gkgs, n)     = ((gkgsInsert gh1 gkgs, n + 1), n)
                traceEvent ("  atomicModifyIORef' gkgsRef") $ pure ()
                n0          <- atomicModifyIORef' gkgsRef f
                traceEvent "  atomicModifyIORef'_ genHsRef" $ pure ()
                atomicModifyIORef'_ genHsRef (Seq.|> gh1)
                inc1TVar wakeAllThreads
                when (gbTrace .&. (gbTQueues .|. gbTProgressChars) /= 0) $ do
                    putS "d"
                    let d       = headTotDeg g1
                    gDShown     <- readIORef gDShownRef
                    when (d /= gDShown) $ do
                        putS $ show d ++ " "
                        writeIORef gDShownRef d
                traceEvent ("  addGenHN end " ++ show n0) $ pure ()
    gMGisRef        <- newIORef Seq.empty   :: IO (IORef (Seq.Seq (Maybe GBGenInfo)))
    ijcsRef         <- newIORef SL.Nil      :: IO (IORef SSPairs)   -- ascending by hEvCmp
    let newIJCs     = do
            ghs0        <- readIORef genHsRef
            ijcs0       <- readIORef ijcsRef
            let f gMGis = (gMGis Seq.|> Just tGi, (gMGis, t, gh, tGi))
                  where
                    t       = Seq.length gMGis
                    ~gh     = traceEvent ("  newIJCs start " ++ show t) $ Seq.index ghs0 t
                    ~tGi    = giNew gh
            mx          <- maybeAtomicModifyIORef gMGisRef ((< Seq.length ghs0) . Seq.length) f
            case mx of
                Nothing                     -> pure False
                Just (gMGis0, t, gh, tGi)   -> do
                    let (skipIs, skipIJCs, addITCs)     =
                            updatePairs nVars evCmp (toList gMGis0) ijcs0 tGi
                        skipIF s i  = Seq.update i Nothing s
                    unless (null skipIs) $      -- 'unless' for speed
                        atomicModifyIORef'_ gMGisRef (\ms -> foldl' skipIF ms skipIs)
                    let ijcsF ijcs  = (ijcs', (ijcs, ijcs'))
                          where
                            ijcs'       =
                                slMergeBy hEvCmp (slMinusSorted hEvCmp ijcs skipIJCs) addITCs
                    (ijcs, ijcs')   <- atomicModifyIORef' ijcsRef ijcsF
                    -- @@@ pure (evElts ijcs')     -- @@ test (time) w/o this (& w/o gbTQueues) on many cores
                    when (null ijcs && not (null ijcs')) $ inc1TVar wakeAllThreads
                    when (gbTrace .&. gbTQueues /= 0) $ do
                        let n       = length ijcs
                            n'      = length ijcs'
                        when (n' < n || n' > n + 10) $
                            putStr $ 'p' : show n ++ "-" ++ show n' ++ " "
                        when ((t + 1) `rem` 50 == 0) $
                            putStr $ 'p' : show (t + 1) ++ ":" ++ show n' ++ " "
                    when (gbTrace .&. gbTProgressInfo /= 0) $
                        putStrLn $ " g" ++ show t ++ ": " ++ _showEV (phP gh)
                    traceEvent ("  newIJCs done " ++ show t) $ pure True
    rgsRef          <- newIORef []          :: IO (IORef [(EPoly c, Int)])
    rgsMNGensRef    <- newIORef (Just 0)    :: IO (IORef (Maybe Int))   -- Nothing if locked
    let checkRgs1   = do    -- may add 1 gh to rgs
            mk          <- readIORef rgsMNGensRef   -- for speed, to avoid atomicModifyIORef'
            case mk of
                (Just k)    -> do
                    ghs         <- readIORef genHsRef
                    if k < Seq.length ghs then do
                        let f mk1   = if mk1 == mk then (Nothing, True) else (mk1, False)
                        res         <- atomicModifyIORef' rgsMNGensRef f
                        when res $ do
                            rgs         <- readIORef rgsRef
                            let gh      = Seq.index ghs k
                            -- @@@ pure (ssRTails (phP gh))    -- @@@ check ok (search for "rg"s)
                            rgs'        <- rgsInsert gh k rgs
                            atomicWriteIORef' rgsRef rgs'
                            atomicWriteIORef' rgsMNGensRef (Just (k + 1))
                            when (gbTrace .&. gbTQueues /= 0) $ do
                                rNTrace     <- readIORef rNTraceRef
                                when (rNTrace > 0) $ do
                                    putChar 'r'
                                    when (rNTrace > 1) $ putStr $ show rNTrace ++ " "
                                    writeIORef rNTraceRef 0
                                when ((k + 1) `rem` 50 == 0) $
                                    putStr $ "rg" ++ show (k + 1) ++ " "
                        pure res
                    else pure False
                Nothing     -> pure False
    -- nextGenHNs holds the nonzero output of S-pair reduction threads for the main thread:
    nextGenHNs      <- newIORef Seq.empty   :: IO (IORef (Seq.Seq (EPolyHDeg c, Int)))
    numForGHNsRef   <- newIORef 0           :: IO (IORef Int)
        -- includes temporary nextGenHNs removals
    let limForGHNs  = 3 * nCores `quot` 2    -- e.g. for preserving cache space(?); @@ tune
        incFGHNs n fromChooseGHN    = do
            if n >= 0 then inc numForGHNsRef n else do
                n0          <- atomicModifyIORef' numForGHNsRef (\m -> (m + n, m))
                when ((n0 > limForGHNs || fromChooseGHN {- nextGenHNs restored -})
                        && n0 + n <= limForGHNs) $
                    inc1TVar wakeAllThreads
        newNextGenHN ghn@(EPolyHDeg g _h, _kN) dn   =
            if ssIsZero g then incFGHNs dn False else do
                traceEvent "  newNextGenHN" $ pure ()
                -- let ghn     = (EPolyHDeg (ssForceTails g) h, kN)    -- @@@ don't force
                ghns0       <- atomicModifyIORef' nextGenHNs (\ghns -> (ghns Seq.|> ghn, ghns))
                incFGHNs (dn + 1) False  -- trying to limit/avoid atomicModifyIORef' calls
                when (null ghns0) $ inc1TVar wakeMainThread
        newG (SPair i j h c)      = {-# SCC newG #-} do
            let ~s  = " start spair(g" ++ show i ++ ",g" ++ show j ++ "): sugar degree " ++
                        show h ++ ", lcm of heads " ++ epShow (SSNZ (rOne cField) c SSZero)
            when (gbTrace .&. gbTProgressDetails /= 0) $ putStrLn s
            traceEvent "  newG" $ pure ()
            -- @@@ inc nSPairsRedRef 1
            ghs     <- readIORef genHsRef
            ghn     <- reduce_n
                        (EPolyHDeg (sPoly (phP (Seq.index ghs i)) (phP (Seq.index ghs j)) c) h)
            newNextGenHN ghn (-1)
            pure True
        doSP        = do
            let f nFGHNs    = (nFGHNs + 1, ())
            mOk         <- maybeAtomicModifyIORef' numForGHNsRef (<= limForGHNs) f
            if isNothing mOk then pure False else do
                mSp         <- slPop ijcsRef
                case mSp of
                    Just sp     -> newG sp
                    Nothing     -> do
                        inc numForGHNsRef (-1)
                        pure False
        chooseGenHN     = do
            traceEvent "  chooseGenHN" $ pure ()
            ghns    <- atomicModifyIORef' nextGenHNs (\ghns -> (Seq.empty, ghns))
            when gbTQueues1 $ do
                let n   = Seq.length ghns
                when (n > nCores + 10) $ putStr $ 'c' : show n ++ " "   -- # "candidates"
            if Seq.null ghns then pure False else do
                let j       = minIndexBy ghnCmp ghns
                    ghn     = Seq.index ghns j
                    ghns1   = Seq.deleteAt j ghns
                atomicModifyIORef'_ nextGenHNs (ghns1 Seq.><)
                traceEvent "  chooseGenHN >< done" $ incFGHNs (-1) True
                addGenHN ghn
                pure True
    numSleepingRef      <- newIORef 0       :: IO (IORef Int)   -- not counting main thread
    -- @@@ testRef             <- newCounter 0
    let checkQueues t   = do
            {- whileM $ do incrCounter_ 1 testRef; (< 1_000_000_000_000) <$> getCPUTime
            do
                n           <- readCounter testRef
                putStrLn $ "\n#" ++ show n -}
            loop
          where
            doEndReduce = do
                ghs         <- readIORef genHsRef
                let kN'     = Seq.length ghs
                mghn        <- maybeDequeueRefSeq nextGenHNs (\(_, kN) -> kN < kN')
                case mghn of
                    Just (gh, kN)   -> do
                        ghn'        <- endReduce_n kN gh
                        newNextGenHN ghn' (-1)
                        pure True
                    Nothing         -> pure False
            tasks       = [checkRgs1 | t == 1] ++   -- @@ tune:
                if      3 * t < nCores then [newIJCs, doSP, doEndReduce]
                -- @@@ else if 2 * t < nCores then [doSP, doEndReduce, newIJCs]
                else                        [doEndReduce, doSP, newIJCs]
            loop        = do
                wake0       <- readTVarIO wakeAllThreads
                q           <- orM tasks
                unless q $ do
                    traceEvent ("  sleep " ++ show t) $ pure ()
                    when (gbTrace .&. gbTQueues /= 0) $ putChar 's'
                    n1          <- atomicModifyIORef' numSleepingRef (dupe . (+ 1))
                    when (n1 == nCores - 1) $ inc1TVar wakeMainThread
                    atomically $ do
                        wake1       <- readTVar wakeAllThreads
                        when (wake1 == wake0) retry
                    inc numSleepingRef (-1)
                loop
    auxThreadIds        <- forM [1 .. nCores - 1] (\t -> forkOn t (checkQueues t))
    mapM_ addGenHN (sortBy ghnCmp [(EPolyHDeg g (epHomogDeg0 g), 0) | g <- initGens])
    let traceTime   = do
            cpuTime2        <- getCPUTime
            cpuTime1        <- readIORef cpuTime1Ref
            when (cpuTime2 - cpuTime1 > 1_000_000_000_000) $ do
                s               <- cpuElapsedStr cpuTime0 sysTime0
                putStrLn $ ' ' : s
                writeIORef cpuTime1Ref cpuTime2
                numSleeping <- readIORef numSleepingRef
                ghs         <- readIORef genHsRef
                rgsMNGHs    <- readIORef rgsMNGensRef
                rgs         <- readIORef rgsRef
                gMGis       <- readIORef gMGisRef
                ijcs        <- readIORef ijcsRef
                numFGHNs    <- readIORef numForGHNsRef
                putStr $
                    show (Seq.length ghs) ++ " gens, " ++
                    maybe "busy" show rgsMNGHs ++ " rg'd, " ++
                    show (length rgs) ++ " rgs, " ++    -- @@@ omit?
                    show (Seq.length gMGis) ++ " paired, " ++
                    show (length ijcs) ++ " pairs, " ++
                    show numFGHNs ++ " for next gens, " ++
                    if numSleeping > 0 then show numSleeping ++ " sleeping, " else ""
    whileM $ do
        when (gbTrace /= 0) traceTime
        wakes0      <- mapM readTVarIO [wakeAllThreads, wakeMainThread]
        let doSleep = do
                numSleeping <- readIORef numSleepingRef
                wakes1      <- mapM readTVarIO [wakeAllThreads, wakeMainThread]
                let res     = wakes1 /= wakes0 || numSleeping < nCores - 1
                when res $ do
                    traceEvent "  SLEEP" $ pure ()
                    when (gbTrace .&. gbTQueues /= 0) $ putChar 'S'
                    atomically $ do
                        wakes2      <- mapM readTVar [wakeAllThreads, wakeMainThread]
                        when (wakes2 == wakes0) retry
                pure res
        orM [chooseGenHN, newIJCs, checkRgs1, doSP, doSleep]
    when (gbTrace .&. gbTSummary /= 0) $ printThreadCapabilities "\n" auxThreadIds
    mapM_ killThread auxThreadIds
    ghs         <- readIORef genHsRef
    let ghsL    = toList ghs
    gMGisL      <- toList <$> readIORef gMGisRef
    when (gbTrace .&. gbTSummary /= 0) $ do
        t           <- cpuElapsedStr cpuTime0 sysTime0
        putStrLn $ "Groebner Basis CPU/Elapsed Times: " ++ t
        nSPairsRed  <- readIORef nSPairsRedRef
        putStrLn $ "# SPairs reduced = " ++ show nSPairsRed
        nRedSteps   <- readIORef nRedStepsRef
        putStrLn $ "# reduction steps (quotient terms) = " ++ show nRedSteps
            -- Macaulay just counts top-reduced
        let ndhs    = [(ssNumTerms g, headTotDeg g, h) | EPolyHDeg g h <- ghsL]
        putStrLn $ "generated (redundant) basis has " ++ show (Seq.length ghs) ++
            " elements with " ++ show (sum (map fst3 ndhs)) ++ " monomials"
        when (gbTrace .&. gbTProgressDetails /= 0) $ do
            putStrLn "(whether used & head degree + sugar, # monomials):"
            let show4 (n, d, h) m   =
                    let dh  = fromIntegral h - d
                    in  maybe "x" (const "") m ++ show d ++
                            (if dh > 0 then '+' : show dh else "") ++ "," ++ show n
            mapM_ (putStrLn . unwords) (chunksOf 10 (zipWith show4 ndhs gMGisL))
    let gsL     = map phP ghsL
        gb      =   -- @@@ or use rgs!?:
            {- mapM reduce2NZ $ -} sortBy (evCmp `on` ssDegNZ)
                (concat (zipWith (\ g mev -> [g | isJust mev]) gsL gMGisL))
        ~s      = show (length gb) ++ " generators"
    if gbTrace .&. gbTResults /= 0 then do
        putStrLn (s ++ ":")
        mapM_ (putStrLn . epShow) gb
    else when (gbTrace .&. gbTSummary /= 0) $ putStrLn s
    {- when (gbTrace .&. gbTQueues /= 0) $ do
        hFlush stdout
        callCommand "echo; ps -v" -}
    pure gb
  where
    _showEV SSZero  = "0"
    _showEV p       = if ssNumTerms p < 10 then epShow (withRing cField ssMonicize p)
                      else epShow (SSNZ (rOne cField) (ssDegNZ p) SSZero) ++ "+... ("
                            ++ show (ssNumTerms p) ++ " terms)"
    sPoly           :: EPoly c -> EPoly c -> ExponVec -> EPoly c
    sPoly f g c     =   -- f and g are nonzero and monic, c = lcm (ssDegNZ f) (ssDegNZ g)
        {-# SCC sPoly #-}
        {- trace ("sPoly: " ++ _showEV f ++ ", " ++ _showEV g ++ ", " ++ show c) $ -}
        withAG (rAG epRing) (-.) (shift f) (shift g)
      where
        shift p     = ssShift (evPlus nVars (fromJust (evMinusMay nVars c (ssDegNZ p))))
                        (ssTail p)
    hEvCmp          = spCmp evCmp True          :: Cmp SPair
    ghnCmp (EPolyHDeg g1 h1, n1) (EPolyHDeg g2 h2, n2)      =
        compare h1 h2 <> ssDegCmp evCmp True g1 g2 <> compare n2 n1
