{-# LANGUAGE Strict, TupleSections #-}

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

import Control.Monad (liftM, replicateM, replicateM_, when, void)
import Data.Array.IArray (Array, (!), listArray)
import Data.Foldable (find, foldl', foldlM, minimumBy, toList)
import Data.List (deleteBy, elemIndex, findIndices, groupBy, insertBy, partition, sortBy)
import Data.List.Extra (chunksOf, mergeBy)
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe, mapMaybe)
import qualified Data.Sequence as Seq
import Data.Tuple.Extra (fst3)
import Numeric (showFFloat)

import Control.Concurrent (forkIO, myThreadId, threadCapability)
import Control.Concurrent.MVar (newEmptyMVar, takeMVar, tryPutMVar)
import Control.Concurrent.STM.TVar (TVar, newTVarIO, readTVar, writeTVar)
import Control.Monad.STM (atomically, retry)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)

import Data.Time.Clock.System (SystemTime(..), getSystemTime)
-- import Debug.Trace
import System.CPUTime (getCPUTime)
import System.IO (hPutChar, hPutStr, stderr)


inc             :: IORef Int -> Int -> IO ()
inc ref n       = when (n /= 0) $ atomicModifyIORef' ref  (\tot -> (tot + n, ()))

elapsedMicroSecs    :: SystemTime -> IO Integer
elapsedMicroSecs (MkSystemTime s0 ns0)      = do
    MkSystemTime s ns       <- getSystemTime
    pure $ 1_000_000 * fromIntegral (s - s0)
        + fromIntegral ns `quot` 1000 - fromIntegral ns0 `quot` 1000

putCPUElapsed                       :: Integer -> SystemTime -> IO ()
putCPUElapsed cpuTime0 sysTime0     = do
    t       <- getCPUTime
    t1      <- elapsedMicroSecs sysTime0
    putStr (showMicroSecs (quot (t - cpuTime0) 1_000_000) ++ "/" ++ showMicroSecs t1 ++ " ")
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
updatePairs         :: Int -> Cmp ExponVec -> [Maybe GBGenInfo] -> [SPair] -> GBGenInfo ->
                        ([Maybe GBGenInfo], [SPair])        -- each [SPair] is ascending
updatePairs nVars evCmp gMGis ijcs tGi      =
    (gMGis' ++ [Just tGi], mergeBy hEvCmp ijcs'' (sortBy hEvCmp itcs'))
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
    skipQs          = zipWith skipQ gMGis itmcs     -- newly redundant gens
      where
        skipQ (Just gi) (Just c)    = divEq (giEv gi) c
        skipQ _         _           = False
    skips           = findIndices id skipQs
    gMGis'          = if null skips then gMGis else     -- for efficiency
                      zipWith (\m q -> if q then Nothing else m) gMGis skipQs
    ijcs'           = if null skips then ijcs else      -- for efficiency
                      filter (\(SPair i j _ _) -> not (i `elem` skips || j `elem` skips)) ijcs
    ijcs''          = filter (\(SPair i j _ c) -> not (evDivs tEv c && ne i c && ne j c)) ijcs'
      where             -- criterion B_ijk
        ne i c      = maybe False (\itc -> not (divEq itc c)) (itmcsA ! i)
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
      where             -- criterion F_jk and Buchberger's 2nd criterion
        buch2 (SPair i j _ c)     = assert (j == t)
            (totDeg (fromJust (gMEvsA ! i)) + totDeg tEv == totDeg c)


data SizedEPoly c   = SizedEPoly { sepN :: Int, sepP :: EPoly c }

sizeEP              :: EPoly c -> SizedEPoly c
sizeEP p            = SizedEPoly (ssNumTerms p) p

-- nVars > 0, each enpss has increasing es, all p /= 0, (ssDegNZ p) unique:
type KerGens c      = Seq.Seq [(Word, [SizedEPoly c])]

type GapsKerGens c  = [(Word, KerGens c)]   -- gaps increasing, 0 gap always present

kgsNew              :: Int -> KerGens c
kgsNew nVars        = Seq.replicate nVars []

gkgsNew             :: Int -> GapsKerGens c
gkgsNew nVars       = [(0, kgsNew nVars)]

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
        ins             :: Op1 [(Word, [SizedEPoly c])]
        ins []          = [(m, [np])]
        ins enpss@(enps@(e, ~nps) : ~t)
            | m < e     = (m, [np]) : enpss
            | m == e    = (m, insertBy kgsSepCmp np nps) : t
            | otherwise = enps : ins t
    in  Seq.adjust' ins v kgs

gkgsInsert          :: forall c. EPolyHDeg c -> Op1 (GapsKerGens c)
gkgsInsert (EPolyHDeg p hDeg)     = go    -- p /= 0, nVars > 0
  where
    gap                     = hDeg - totDeg (ssDegNZ p)
    go (h@(gap0, kgs0) : t) = assert (gap >= gap0) $
        if gap == gap0 then (gap, kgsInsert p kgs0) : t
        else if null t || gap < fst (head t) then
            h : (gap, kgsInsert p (kgsNew (Seq.length kgs0))) : t
        else h : go t
    go []                   = undefined

kgsDelete           :: forall c. EPoly c -> Op1 (KerGens c)
kgsDelete p kgs     =       -- p in kgs (so p /= 0, nVars > 0), (ssDegNZ p) unique in kgs
    assert (not (ssIsZero p) && Seq.length kgs > 0) $
    let nVars   = Seq.length kgs
        es      = exponsL nVars (ssDegNZ p)
        m       = maximum es
        v       = fromJust (elemIndex m es)
        np      = sizeEP p
        eq np1 np2      = kgsSepCmp np1 np2 == EQ
        del             :: Op1 [(Word, [SizedEPoly c])]
        del []          = undefined
        del (enps@(e, ~nps) : t)
            | m > e     = enps : del t
            | m == e    = assert (isJust (find (eq np) nps)) (m, deleteBy eq np nps) : t
            | otherwise = undefined
    in  Seq.adjust' del v kgs

gkgsDelete          :: forall c. EPolyHDeg c -> Op1 (GapsKerGens c)
gkgsDelete (EPolyHDeg p hDeg)     = go      -- p in gkgs (so p /= 0, nVars > 0),
                                            -- (ssDegNZ p) unique in gkgs
  where
    gap                     = hDeg - totDeg (ssDegNZ p)
    go (h@(gap0, kgs0) : t) = assert (gap >= gap0) $
        if gap == gap0 then (gap, kgsDelete p kgs0) : t
        else h : go t
    go []                   = undefined

-- kgsReplace              :: EPoly c -> EPoly c -> Op1 (KerGens c)
-- kgsReplace p p' kgs     = kgsInsert p' (kgsDelete p kgs)

gkgsReplace             :: EPolyHDeg c -> EPolyHDeg c -> Op1 (GapsKerGens c)
gkgsReplace ph ph' gkgs = gkgsInsert ph' (gkgsDelete ph gkgs)

{-# SCC kgsFindReducer #-}
kgsFindReducer          :: forall c. EPoly c -> KerGens c -> Maybe (EPoly c)
kgsFindReducer p kgs    =
    if ssIsZero p then Nothing else
    let nVars   = Seq.length kgs
        pEv     = ssDegNZ p
        npsF bnp                   []                           = bnp
        npsF bnp@(SizedEPoly bn _) (ng@(SizedEPoly n ~g) : ~t)
            | bn <= n   = bnp
            | otherwise = npsF (if evDivides nVars (ssDegNZ g) pEv then ng else bnp) t
        esF bnp _  []   = bnp
        esF bnp pe ((e, ~nps) : ~t)
            | pe < e    = bnp
            | otherwise = esF (npsF bnp nps) pe t
        vF bnp (pe, enpss)      = esF bnp pe enpss
        resSep  = foldl' vF (SizedEPoly (maxBound :: Int) SSZero)
                    (zip (exponsL nVars pEv) (toList kgs))
    in  if sepN resSep < (maxBound :: Int) then Just (sepP resSep) else Nothing

gkgsFindReducer         :: forall c. EPoly c -> GapsKerGens c -> Maybe (EPolyHDeg c)
gkgsFindReducer p gkgs  = listToMaybe (mapMaybe find1 gkgs)
  where
    find1 (gap, kgs)    =
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
gkgsTopReduce div2 kerVar nRedStepsRef      = go
  where
    go ph@(EPolyHDeg p _)    = do
        (ker, nGens)    <- kerVar
        let go1 gh      = do
                let (rh, nSteps)    = sugarReduce div2 ph gh
                inc nRedStepsRef nSteps
                go rh
        maybe (pure (ph, nGens)) go1 (gkgsFindReducer p ker)

kgsReduce               :: (EPoly c -> EPoly c -> (EPoly c, EPoly c)) -> KerGens c -> EPoly c ->
                            (EPoly c, Int)
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

foldReduce1                 :: forall c f. Foldable f => Int ->
                                (EPoly c -> EPoly c -> (EPoly c, EPoly c)) -> f (EPolyHDeg c) ->
                                EPolyHDeg c -> Maybe (EPolyHDeg c, Int)
foldReduce1 nVars div2 ghs ph@(EPolyHDeg p _)   =       -- all gs /= 0
    if ssIsZero p then Nothing else
    let pEv     = ssDegNZ p
        mgh     = find (\gh -> evDivides nVars (ssDegNZ (phP gh)) pEv) ghs
    in  fmap (sugarReduce div2 ph) mgh


-- | gbTrace bits for 'groebnerBasis' tracing. Bits 0x0F are useful to end users.
gbTSummary, gbTProgressChars, gbTProgressInfo, gbTResults, gbTQueues, gbTProgressDetails  :: Int
gbTSummary          = 0x01  -- ^ a short summary at the end of a run
gbTProgressChars    = 0x02  -- ^ 'o' character or total degree for each s-poly reduction result
gbTProgressInfo     = 0x04  -- ^ info when adding or removing a generator
gbTResults          = 0x08  -- ^ output final generators
gbTQueues           = 0x10  -- ^ info about threads and their queues
gbTProgressDetails  = 0x20  -- ^ details relating to selection strategy

groebnerBasis       :: forall c. Int -> Cmp ExponVec -> Field c -> Ring (EPoly c) -> [EPoly c]
                        -> Int -> Int -> (EPoly c -> String) -> IO [EPoly c]
groebnerBasis nVars evCmp cField epRing initGens nCores gbTrace epShow    = do
    cpuTime0        <- getCPUTime
    sysTime0        <- getSystemTime
    gkgsRef         <- newIORef (gkgsNew nVars, 0)  -- (gkgs, # gens)
    nRedStepsRef    <- newIORef 0
    nSPairsRedRef   <- newIORef 0
    let topDiv2     = rBDiv2 epRing False
        topReduce   = gkgsTopReduce topDiv2 (readIORef gkgsRef) nRedStepsRef
        reduce2 SSZero          = pure SSZero
        reduce2 (SSNZ c d t)    = do
            ((0, kgs) : _, _)       <- readIORef gkgsRef
            let (t', nSteps)        = kgsReduce topDiv2 kgs t
            inc nRedStepsRef nSteps
            pure (SSNZ c d t')
        reduce_n gh = do
            (EPolyHDeg g1 h1, n)    <- topReduce gh
            g2                      <- reduce2 (ssForceTails g1)
            pure (EPolyHDeg g2 h1, n)
        reduce gh   = liftM fst (reduce_n gh)
    genHsRef        <- newIORef Seq.empty :: IO (IORef (Seq.Seq (EPolyHDeg c)))
    let gap0NZ (EPolyHDeg g h)  = if h /= totDeg (ssDegNZ g) then Nothing else Just g
        endReduce kN gh         = do
            ghs         <- readIORef genHsRef
            if kN == length ghs || ssIsZero (phP gh) then pure gh else
                let endGHs      = Seq.drop kN ghs
                    mghn        = foldReduce1 nVars topDiv2 endGHs gh
                    endRed1 (ph, nSteps)    = do
                        inc nRedStepsRef nSteps
                        reduce ph
                    endRed2 (EPolyHDeg (SSNZ c d t) h)  = do
                        let g0s                 = mapMaybe gap0NZ (toList endGHs)
                            (todo, t', nSteps)  = foldReduce nVars topDiv2 g0s t
                        inc nRedStepsRef nSteps
                        p       <- (if todo then reduce2 else pure) (SSNZ c d t')
                        pure (EPolyHDeg p h)
                    endRed2 (EPolyHDeg SSZero _)        = undefined
                in  maybe (endRed2 gh) endRed1 mghn
    -- rgs is a [(g, i)] of nonzero g with descending (ssDegNZ g)
    let rgsInsert   :: EPolyHDeg c -> Int -> [(EPoly c, Int)] -> IO [(EPoly c, Int)]
        rgsInsert (EPolyHDeg g _) i []                  = pure [(g, i)]
        rgsInsert gh@(EPolyHDeg g gHDeg) i rgs@((h, j) : t)
            | evCmp (ssDegNZ g) (ssDegNZ h) == GT       = pure ((g, i) : rgs)
            | evDivides nVars (ssDegNZ g) (ssDegNZ h)   = do
                when (gbTrace .&. gbTProgressInfo /= 0) $
                    putStrLn $ "remove g" ++ show j ++ " (" ++ _showEV h ++ ") by g" ++ show i
                        ++ " (" ++ _showEV g ++ ")"
                ghs     <- readIORef genHsRef
                let hh  = Seq.index ghs j
                atomicModifyIORef' gkgsRef (\(gkgs, n) -> ((gkgsDelete hh gkgs, n), ()))
                rgsInsert gh i t
            | otherwise                                 = do
                t'          <- rgsInsert gh i t
                if gHDeg /= totDeg (ssDegNZ g) then pure ((h, j) : t') else do
                    let (q, r)  = rBDiv2 epRing True h g
                    if ssIsZero q then pure ((h, j) : t') else do
                        inc nRedStepsRef (ssNumTerms q)
                        when (gbTrace .&. gbTQueues /= 0) $
                            if totDeg (ssDegNZ q) == 0 then putStr "a " else
                                putStrLn $ "reduce g" ++ show j ++ " (" ++ _showEV h ++ ") by g"
                                    ++ show i ++ " (" ++ _showEV g ++ ")"
                        r'          <- if totDeg (ssDegNZ q) == 0 then pure r else reduce2 r
                        ghs0        <- readIORef genHsRef
                        let hh      = Seq.index ghs0 j
                            rh'     = EPolyHDeg r' (phH hh)
                        atomicModifyIORef' gkgsRef
                            (\(gkgs, n) -> ((gkgsReplace hh rh' gkgs, n), ()))
                        atomicModifyIORef' genHsRef (\ghs -> (Seq.update j rh' ghs, ()))
                        assert (not (ssIsZero r')) (pure ((r', j) : t'))
        addGenHN arg@(gMGis, ijcs, rgs) (gh, kN)    = {-# SCC addGenHN #-} do
            EPolyHDeg g0 h         <- (if kN == 0 then reduce else endReduce kN) gh
            if ssIsZero g0 then do
                when (gbTrace .&. gbTProgressChars /= 0) (hPutChar stderr 'o')
                pure arg
            else do
                let g1      = withRing cField ssMonicize g0
                    gh1     = EPolyHDeg g1 h
                atomicModifyIORef' gkgsRef (\(gkgs, n) -> ((gkgsInsert gh1 gkgs, n + 1), ()))
                k           <- atomicModifyIORef' genHsRef
                                (\ghs -> (ghs Seq.|> gh1, Seq.length ghs))
                rgs'        <- rgsInsert gh1 k rgs
                let (gMGis', ijcs')     = updatePairs nVars evCmp gMGis ijcs (giNew gh1)
                when (gbTrace .&. gbTProgressChars /= 0) $ do
                    let s       = show (headTotDeg g1)
                    hPutStr stderr (if length s > 1 then ' ':s++"," else s)
                when (gbTrace .&. gbTProgressInfo /= 0) $
                    putStrLn $ " (" ++ show (length ijcs') ++ " unqueued pairs) + g" ++ show k
                        ++ ": " ++ _showEV g1
                pure (gMGis', ijcs', rgs')
    -- nextGenHNs holds the output of S-pair reduction threads for the main thread:
    nextGenHNs      <- newIORef [] :: IO (IORef [(EPolyHDeg c, Int)])
    checkNextGens   <- newEmptyMVar
    let newG (SPair i j h c)      = {-# SCC newG #-} do
            let ~s  = "start spair(g" ++ show i ++ ",g" ++ show j ++ "): sugar degree " ++
                        show h ++ ", lcm of heads " ++ epShow (SSNZ (rOne cField) c SSZero)
            when (gbTrace .&. gbTProgressDetails /= 0) $ putStrLn s
            ghs     <- readIORef genHsRef
            (EPolyHDeg g h', kN) <- reduce_n
                        (EPolyHDeg (sPoly (phP (Seq.index ghs i)) (phP (Seq.index ghs j)) c) h)
            let g'  = ssForceTails g
            atomicModifyIORef' nextGenHNs (\ngs -> ((EPolyHDeg g' h', kN) : ngs, ()))
            _   <- tryPutMVar checkNextGens ()
            pure ()
    nextSPairs      <- newTVarIO (Just []) :: IO (TVar (Maybe [SPair]))     -- sorted
    let commitSPairs nMax ijcs  = do
            let (as, bs)    = splitAt nMax ijcs
            atomically $ do
                nextSPs     <- readTVar nextSPairs
                writeTVar nextSPairs (Just (mergeBy hEvCmp (fromJust nextSPs) as))
            pure (length as, bs)
        forkMakeGs              = forkIO loop
          where
            loop        = do
                mSp         <- atomically $ do
                    nextSPs     <- readTVar nextSPairs
                    let doSps []        = retry
                        doSps (sp : ~t) = do
                            writeTVar nextSPairs (Just t)
                            pure (Just sp)
                    maybe (pure Nothing) doSps nextSPs
                maybe (pure ()) (\sp -> newG sp >> loop) mSp
    auxThreadIds        <- replicateM (nCores - 1) forkMakeGs
    let showCapabilities    = do
            mainThreadId        <- myThreadId
            capInfos            <- mapM threadCapability (mainThreadId : auxThreadIds)
            putStr "\nThreads are on capabilities: "
            mapM_ (putStrLn . unwords) (chunksOf 32 (map (show . fst) capInfos))
        go arg@(gMGis, ijcs, rgs) nextGHNs numForThreads
            | let n = 2 * nCores - 1 - numForThreads - (length nextGHNs + 1) `quot` 2,  -- @@ tune
              n > 0 && not (null ijcs)      = do
                (m, ijcs')      <- commitSPairs n ijcs
                go (gMGis, ijcs', rgs) nextGHNs (numForThreads + m)
            | not (null nextGHNs) || numForThreads > 0          = do
                nextGHNs'   <- atomicModifyIORef' nextGenHNs ([], )
                inc nSPairsRedRef (length nextGHNs')
                when (gbTrace .&. gbTQueues /= 0 && length nextGHNs' > 1) $
                    putStr ("n" ++ show (length nextGHNs') ++ " ")
                if not (null nextGHNs') then do
                    let (zs, nzs)   = partition (ssIsZero . phP . fst) nextGHNs'
                    when (gbTrace .&. gbTProgressChars /= 0) $
                        replicateM_ (length zs) (hPutChar stderr 'o')
                    let nextGHNs''  = mergeBy ghnCmp nextGHNs (sortBy ghnCmp nzs)
                    go arg nextGHNs'' (numForThreads - length nextGHNs')
                else if null nextGHNs then do
                    (m, ijcs')      <- commitSPairs 1 ijcs
                    when (gbTrace .&. gbTQueues /= 0) $ do
                        putChar 'w'
                        putCPUElapsed cpuTime0 sysTime0
                    mSp         <- atomically $ do
                        nextSPs     <- readTVar nextSPairs
                        let sPs     = fromJust nextSPs
                        if null sPs then pure Nothing else do
                            writeTVar nextSPairs (Just (tail sPs))
                            pure (Just (head sPs))
                    case mSp of
                        Nothing     -> void $ takeMVar checkNextGens
                        Just sp     -> do
                            -- @@ tune? add some nextSPs, or wait, or see if nextGHNs were 0s ??
                            when (gbTrace .&. gbTQueues /= 0) $ putStr "newG "
                            newG sp
                    when (gbTrace .&. gbTQueues /= 0) $ putCPUElapsed cpuTime0 sysTime0
                    go (gMGis, ijcs', rgs) nextGHNs (numForThreads + m)
                else do
                    when (gbTrace .&. gbTQueues /= 0) $ do
                        putStr $ "TGOP" ++  -- # terms, gens, output queue, pairs
                            show (snd (head nextGHNs), length rgs, length nextGHNs, length ijcs)
                        when (length rgs `mod` 10 == 0) $ putChar '\n'
                    arg1        <- addGenHN arg (head nextGHNs)
                    go arg1 (tail nextGHNs) numForThreads
            | otherwise         = {-# SCC gbDone #-} do
                when (gbTrace .&. gbTSummary /= 0) showCapabilities
                atomically (writeTVar nextSPairs Nothing)
                ghs         <- readIORef genHsRef
                let ghsL    = toList ghs
                when (gbTrace .&. gbTSummary /= 0) $ do
                    putStr "Groebner Basis CPU/Elapsed Times: "
                    putCPUElapsed cpuTime0 sysTime0
                    nSPairsRed  <- readIORef nSPairsRedRef
                    putStrLn $ "\n# SPairs reduced = " ++ show nSPairsRed
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
                        mapM_ (putStrLn . unwords) (chunksOf 10 (zipWith show4 ndhs gMGis))
                let gsL     = map phP ghsL
                    gb      =   -- @@@ or use rgs!?:
                        {- mapM reduce2NZ $ -} sortBy (evCmp `on` ssDegNZ)
                            (concat (zipWith (\ g mev -> [g | isJust mev]) gsL gMGis))
                when (gbTrace .&. gbTResults /= 0) $ do
                    putStrLn (show (length gb) ++ " generators:")
                    mapM_ (putStrLn . epShow) gb
                pure gb
    let initGHNs        = sortBy ghnCmp [(EPolyHDeg g (epHomogDeg0 g), 0) | g <- initGens]
    (gMGis, ijcs, rgs)  <- foldlM addGenHN ([], [], []) initGHNs
    go (gMGis, ijcs, rgs) [] 0
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
