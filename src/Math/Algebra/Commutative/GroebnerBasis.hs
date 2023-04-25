{-# LANGUAGE Strict #-}

{- |  This module defines functions for computing and using a Groebner Basis.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.Commutative.GroebnerBasis (
    SubmoduleOps(..), fromGens,
    SPair(..), GBPolyOps(..), StdEvCmp(..), secIsGraded,
    gbTSummary, gbTProgressChars, gbTProgressInfo, gbTResults, gbTQueues, gbTProgressDetails,
    GroebnerIdeal, gbiSmOps
) where

import Math.Algebra.General.Algebra

import Control.Monad (forM, unless, void, when)
import Control.Monad.Extra (ifM, orM, whenM, whileM)
import Data.Foldable (find, minimumBy, toList)
import Data.Int (Int64)
import Data.List (elemIndex, findIndices, groupBy, sortBy)
import Data.List.Extra (chunksOf)
import Data.Maybe (catMaybes, fromJust, isJust, listToMaybe, mapMaybe)
import qualified Data.Sequence as Seq
import Data.Tuple.Extra (dupe, fst3)
import qualified Data.Vector as V
import Numeric (showFFloat)
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL

import Control.Concurrent (ThreadId, forkOn, killThread, myThreadId, threadCapability)
import Control.Concurrent.STM.TVar (TVar, modifyTVar', newTVarIO, readTVar, readTVarIO,
    writeTVar)
-- import Control.Monad.Primitive (PrimMonad, PrimState)
import Control.Monad.STM (atomically, retry)
import Control.Parallel.Strategies (parListChunk, rseq, using)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef, writeIORef)
import Data.IORef.Extra (atomicModifyIORef'_, atomicWriteIORef')
-- import Data.Primitive.PrimVar (PrimVar, atomicReadInt, fetchAddInt, newPrimVar)
import qualified Control.Concurrent.Counter as C
import System.IO.Unsafe (unsafePerformIO)

import Data.Time.Clock.System (SystemTime(..), getSystemTime)
import Debug.Trace
import GHC.Stats (RTSStats, getRTSStats, getRTSStatsEnabled, mutator_cpu_ns, mutator_elapsed_ns)
import System.CPUTime (getCPUTime)
import System.IO (hPutStr, stderr)
-- import System.IO (hFlush, stdout)
-- import System.Process (callCommand)


-- | @@ Move and generalize 'SubmoduleOps' (include bDiv and syzygies?):
data SubmoduleOps r m sm    = SubmoduleOps {
    zeroMd      :: sm,                  -- ^ zero module
    plusGens    :: Int -> sm -> [m] -> sm,  -- ^ @plusGens gbTrace@, add any generators
    stdGens     :: Bool -> sm -> Seq.Seq m,     -- ^ \"standard\" generators,
                    -- @stdGens doFullReduce sm@
    bModBy      :: Bool -> sm -> Op1 m  -- ^ @bModBy doFullReduce sm m@
}

fromGens        :: SubmoduleOps r m sm -> Int -> [m] -> sm
-- ^ @fromGens smA gbTrace gens@
fromGens smA gbTrace    = smA.plusGens gbTrace smA.zeroMd


evElts          :: [a] -> ()
-- force all elements of a list
evElts          = foldr seq ()

evList          :: [a] -> [a]
-- force all elements of a list, and return it
evList xs       = evElts xs `seq` xs

{- currently unused
minIndexBy                      :: Cmp a -> Seq.Seq a -> Int
-- The index of the first least element of a nonempty sequence.
minIndexBy cmp (h Seq.:<| t)    = fst (Seq.foldlWithIndex f (0, h) t)
  where
    f im@(_, m) j e     = if cmp m e == GT then (j, e) else im
minIndexBy _   Seq.Empty        = undefined
-}

inc             :: IORef Int -> Int -> IO ()
inc ref n       = when (n /= 0) $ atomicModifyIORef'_ ref (+ n)

inc1TVar        :: TVar Int -> IO ()
inc1TVar var    = atomically $ modifyTVar' var (+ 1)

-- fetchAddInt_        :: PrimMonad m => PrimVar (PrimState m) Int -> Int -> m ()
fetchAddInt_        :: C.Counter -> Int -> IO ()
fetchAddInt_ var    = void . C.add var

slPop           :: TVar (SL.List a) -> IO (Maybe a)
slPop esVar     = atomically $ do
    es      <- readTVar esVar
    f es
  where
    f (h :! t)      = do writeTVar esVar t; pure (Just h)
    f SL.Nil        = pure Nothing

{- currently unused
maybeAtomicModifyIORef'             :: IORef a -> Pred a -> (a -> (a, b)) -> IO (Maybe b)
-- for speed, trying to avoid atomicModifyIORef'
maybeAtomicModifyIORef' ref p f     = do
    a0      <- readIORef ref
    if not (p a0) then pure Nothing else atomicModifyIORef' ref f'
  where
    f' a    = if not (p a) then (a, Nothing) else second Just (f a)

maybeDequeueRefSeq          :: IORef (Seq.Seq a) -> Pred a -> IO (Maybe a)
maybeDequeueRefSeq ref p    = maybeAtomicModifyIORef' ref p' f
  where
    p' (h Seq.:<| _t)   = p h
    p' _                = False
    f (h Seq.:<| t)     = (t, h)
    f _                 = undefined
-}

maybeAtomicModifyTVarIO'            :: TVar a -> Pred a -> (a -> a) -> IO Bool
maybeAtomicModifyTVarIO' var p f    = do
    a0      <- readTVarIO var
    if not (p a0) then pure False else  -- for speed, trying to avoid atomic transaction
        atomically $ do
            a       <- readTVar var
            let res = p a
            when res $ writeTVar var $! f a
            pure res

elapsedNs                           :: SystemTime -> IO Int64
elapsedNs (MkSystemTime s0 ns0)     = do
    MkSystemTime s ns       <- getSystemTime
    pure $ 1_000_000_000 * (s - s0) + fromIntegral ns - fromIntegral ns0

getMaybeRTSStats    :: IO (Maybe RTSStats)
getMaybeRTSStats    = ifM getRTSStatsEnabled (Just <$> getRTSStats) (pure Nothing)

cpuElapsedStr       :: Integer -> SystemTime -> Maybe RTSStats -> IO String
cpuElapsedStr cpuTime0 sysTime0 mStats0     = do
    t       <- getCPUTime
    t1      <- elapsedNs sysTime0
    mutS    <- maybe (pure "") getMutS mStats0
    pure (showNs2 (quot (t - cpuTime0) 1000) t1 ++ mutS)
  where
    showSecs t          = showFFloat (Just 3) (t :: Double) "s"
    fromNs n            = 1e-9 * fromIntegral n :: Double
    showNs n            = showSecs (fromNs n)
    showNs2 cpu elapsed = showNs cpu ++ "/" ++ showNs elapsed ++ "=" ++
                            showFFloat (Just 1) (fromNs cpu / fromNs elapsed) ""
    getMutS stats0      = do
        stats       <- getRTSStats
        let cpu     = mutator_cpu_ns stats - mutator_cpu_ns stats0
            elapsed = mutator_elapsed_ns stats - mutator_elapsed_ns stats0
        pure $ ", MUT " ++ showNs2 cpu elapsed


data SPair ev       = SPair { i, j :: Int, h :: Word, m :: ev }
    -- i, j, "sugar" (homog) degree if useSugar, LCM of head evs of gens i and j

{- | 'GBPolyOps' are the operations on Exponent Vectors @ev@ and Polynomials @p@ that are needed
    by our (Buchberger) Groebner Basis algorithm. An Exponent Vector is abstractly a vector of
    small nonnegative integers, possibly together with its total degree or other weights. Also,
    these polynomials may be reduced modulo some relations, and the exponents may thus have
    bounded degrees. For example, see the "BinPoly" module. -}
data GBPolyOps ev term p    = GBPolyOps {
    evCmp       :: Cmp ev,          -- ^ the chosen monomial order (a total ordering)
    evDivides   :: ev -> ev -> Bool,    -- ^ note args reversed from e.g. 'maybeQuo'
    evLCM       :: Op2 ev,          -- ^ Least Common Multiple
    evTotDeg    :: ev -> Word,
    nEvGroups   :: Int,             -- ^ # of groups of exponents
    evGroup     :: ev -> [Word],    -- ^ totDeg in each group
    evShowPrec  :: ShowPrec ev,     -- ^ e.g. for debugging or logging
    pR          :: Ring p,
    descVarPs   :: [p],             -- ^ more main variables are listed first
    leadEvNZ    :: p -> ev,         -- ^ the argument must be nonzero
    monicizeU   :: Op1 p,           -- ^ the argument must be nonzero, with a unit leading coef
    extraSPairs :: ev -> Int -> Word -> [SPair ev],     -- ^ @extraSPairs ev j h@
    sPoly       :: p -> p -> SPair ev -> p, -- ^ @sPoly f g sp@ assumes @f@ and @g@ are monic
    homogDeg0   :: p -> Word,       -- ^ max totDeg, or 0 for the 0 polynomial
    numTerms    :: p -> Int,
    cons        :: term -> p -> p,  -- ^ the first argument must be more main than the second
    unconsNZ    :: p -> (term, p),  -- ^ the argument must be nonzero
    pShow       :: p -> String,     -- ^ e.g. for debugging or logging
    useSugar    :: Bool             -- ^ use "sugar" (homogeneous degree) heuristic
}


{- See Gebauer & Moller, J. Symbolic Computation (1988) 6, 275-286;
    Giovini, Mora, Niesi, Robbiano, Traverso, "One sugar cube, please ...", 1991: -}

spCmp               :: Cmp ev -> Bool -> Cmp (SPair ev)
spCmp evCmp useSugar (SPair i1 j1 h1 ev1) (SPair i2 j2 h2 ev2)  =
    (if useSugar then (compare h1 h2 <>) else id)
        (evCmp ev1 ev2 <> compare j1 j2 <> compare i1 i2)

type SortedSPairs ev    = SL.List (SPair ev)    -- sorted using (spCmp evCmp useSugar)

data EPolyHDeg p    = EPolyHDeg { p :: p, h :: Word }   -- poly and "sugar" homog degree

data GBGenInfo ev   = GBGenInfo { ev :: ev, dh :: Word }

giNew               :: GBPolyOps ev term p -> EPolyHDeg p -> GBGenInfo ev
-- p /= 0, h is "sugar" (homog) degree
giNew (GBPolyOps { leadEvNZ, evTotDeg }) (EPolyHDeg p h)    =
    let ev      = leadEvNZ p
    in  GBGenInfo ev (h - evTotDeg ev)

{-# SCC updatePairs #-}
updatePairs     :: forall ev term p. GBPolyOps ev term p -> [Maybe (GBGenInfo ev)] ->
                    SortedSPairs ev -> GBGenInfo ev -> ([Int], SortedSPairs ev, SortedSPairs ev)
updatePairs (GBPolyOps { evCmp, evDivides, evLCM, evTotDeg, extraSPairs, useSugar })
    gMGis ijcs tGi      = (skipIs, skipIJCs, addITCs)
  where
    hEvCmp          = spCmp evCmp useSugar      :: Cmp (SPair ev)
    lcmCmp          = evCmp `on` (.m)           :: Cmp (SPair ev)   -- note not a total order
    hCmp            = compare `on` (.h)         :: Cmp (SPair ev)
    giLcm gi1 gi2   = GBGenInfo (evLCM gi1.ev gi2.ev) (max gi1.dh gi2.dh)
    giToSp i j gi   =
        let ev          = gi.ev
        in  SPair i j (gi.dh + evTotDeg ev) ev
    t               = length gMGis
    tEv             = tGi.ev
    itMGis          = map (fmap (giLcm tGi)) gMGis      :: [Maybe (GBGenInfo ev)]
    itmcs           = map (fmap (.ev)) itMGis           :: [Maybe ev]     -- lcms
    itmcsV          = V.fromListN t itmcs               :: V.Vector (Maybe ev)
    divEq ev c      = assert (evDivides ev c) (evTotDeg ev == evTotDeg c)
    skipIQs         = zipWith skipQ gMGis itmcs     -- newly redundant gens
      where
        skipQ (Just gi) (Just c)    = divEq gi.ev c
        skipQ _         _           = False
    skipIs          = evList (findIndices id skipIQs)
    skipIJCs        = SL.filter canSkip ijcs
      where             -- criterion B_ijk
        canSkip (SPair i j _ c)     = i >= 0 && evDivides tEv c && ne i c && ne j c
        ne i c                      = maybe False (\itc -> not (divEq itc c)) (itmcsV V.! i)
    itcs            = catMaybes (zipWith (\i -> fmap (giToSp i t)) [0..] itMGis)  :: [SPair ev]
    -- "sloppy" sugar method:
    itcss           = groupBy (cmpEq lcmCmp) (sortBy lcmCmp itcs)
    itcsToC         = (.m) . head
    itcss'          = filter (noDivs . itcsToC) itcss       -- criterion M_ik
      where
        firstDiv c  = find (\ itcs1 -> evDivides (itcsToC itcs1) c) itcss
        noDivs c    = divEq (itcsToC (fromJust (firstDiv c))) c
    gMEvsV          = V.fromListN t (map (fmap (.ev)) gMGis)    :: V.Vector (Maybe ev)
    bestH           = if useSugar then minimumBy hCmp else head
    itcs'           = mapMaybe (\gp -> if any buch2 gp then Nothing else Just (bestH gp)) itcss'
      where             -- criterion F_jk and Buchberger's 2nd criterion (gi and gt rel. prime)
        buch2 (SPair i j _ c)     = assert (j == t)
            (evTotDeg (fromJust (gMEvsV V.! i)) + evTotDeg tEv == evTotDeg c)
    addITCs         = SL.fromList
                        (sortBy hEvCmp (extraSPairs tEv t (evTotDeg tEv + tGi.dh) ++ itcs'))


data SizedEPoly p   = SizedEPoly { n :: Int, p :: p }

sizeEP               :: (p -> Int) -> p -> SizedEPoly p
sizeEP numTermsF p   = SizedEPoly (numTermsF p) p

data ENPs p         = ENPs { _e :: Word, _nps :: SL.List (SizedEPoly p) }
-- exponent and list of sized polys


data WithNGens a    = WithNGens a Int

wngFirst                    :: (a -> a') -> WithNGens a -> WithNGens a'
wngFirst f (WithNGens a n)  = WithNGens (f a) n


-- nEvGroups > 0, each enpss has increasing es, all p /= 0, (leadEvNZ p) unique:
type KerGens p      = Seq.Seq (SL.List (ENPs p))

data GapKerGens p   = G1KGs { gap :: Word, _kgs :: KerGens p }

type GapsKerGens p  = SL.List (GapKerGens p)    -- gaps increasing, 0 gap always present

data KGsOps p       = KGsOps {
    gkgsEmpty   :: GapsKerGens p,
    gkgsInsert  :: EPolyHDeg p -> Op1 (GapsKerGens p),
    gkgsDelete  :: EPolyHDeg p -> Op1 (GapsKerGens p),
    gkgsReplace :: EPolyHDeg p -> EPolyHDeg p -> Op1 (GapsKerGens p),
    gkgsReduce      :: GapsKerGens p -> Bool -> p -> (p, Int),
        -- reduce a polynomial, counting steps
    gkgsTopReduce   :: IO (WithNGens (GapsKerGens p)) -> EPolyHDeg p ->
                        IO (WithNGens (EPolyHDeg p), Int),
        -- top-reduce a (gh, kN)
    foldReduce      :: forall f. Foldable f => f p -> p -> (Bool, p, Int),
        -- fully reduce by folding (not kgs), except stop and return True if/when a deg > 0
        -- quotient
    foldTopReduce1  :: forall f. Foldable f => f (EPolyHDeg p) -> EPolyHDeg p ->
                        Maybe (EPolyHDeg p, Int)
        -- do 1 folding step if there's a top-reducer
}

kgsOps                      :: forall ev term p. GBPolyOps ev term p -> KGsOps p
kgsOps (GBPolyOps { .. })   = KGsOps { .. }
  where
    pZero       = pR.zero
    pIsZero     = pR.isZero
    topDiv      = pR.bDiv False
    
    kgsEmpty            :: KerGens p
    kgsEmpty            = Seq.replicate nEvGroups SL.Nil
    
    gkgsEmpty           :: GapsKerGens p
    gkgsEmpty           = SL.singleton (G1KGs 0 kgsEmpty)

    kgsSepCmp           :: Cmp (SizedEPoly p)
    kgsSepCmp (SizedEPoly n1 p1) (SizedEPoly n2 p2)   =
        n1 `compare` n2 <> evCmp (leadEvNZ p1) (leadEvNZ p2)

    kgsInsert           :: p -> Op1 (KerGens p)
    kgsInsert p kgs     =       -- p /= 0, nEvGroups > 0
        assert (not (pIsZero p) && Seq.length kgs > 0) $
        let es      = evGroup (leadEvNZ p)
            m       = maximum es
            v       = fromJust (elemIndex m es)
            np      = sizeEP numTerms p
            ins             :: Op1 (SL.List (ENPs p))
            ins SL.Nil      = SL.singleton (ENPs m (SL.singleton np))
            ins enpss@(enps@(ENPs e ~nps) :! ~t)
                | m < e     = ENPs m (SL.singleton np) :! enpss
                | m == e    = ENPs m (SL.insertBy kgsSepCmp np nps) :! t
                | otherwise = enps :! ins t
        in  Seq.adjust' ins v kgs

    gkgsInsert          :: EPolyHDeg p -> Op1 (GapsKerGens p)
    gkgsInsert (EPolyHDeg p hDeg)     = go    -- p /= 0, nEvGroups > 0
      where
        gap                     = if useSugar then hDeg - evTotDeg (leadEvNZ p) else 0
        go (h@(G1KGs gap0 kgs0) :! t)   = assert (gap >= gap0) $
            if gap == gap0 then G1KGs gap (kgsInsert p kgs0) :! t
            else if maybe True ((gap <) . (.gap)) (SL.headMaybe t) then
                h :! G1KGs gap (kgsInsert p kgsEmpty) :! t
            else h :! go t
        go SL.Nil                           = undefined

    kgsDelete           :: p -> Op1 (KerGens p)
    kgsDelete p kgs     =   -- p in kgs (so p /= 0, nEvGroups > 0), (leadEvNZ p) unique in kgs
        assert (not (pIsZero p) && Seq.length kgs > 0) $
        let es      = evGroup (leadEvNZ p)
            m       = maximum es
            v       = fromJust (elemIndex m es)
            np      = sizeEP numTerms p
            eq np1 np2      = kgsSepCmp np1 np2 == EQ
            del             :: Op1 (SL.List (ENPs p))
            del (enps@(ENPs e ~nps) :! t)
                | m > e     = enps :! del t
                | m == e    = assert (isJust (find (eq np) nps)) $
                                ENPs m (SL.deleteBy eq np nps) :! t
                | otherwise = undefined
            del SL.Nil      = undefined
        in  Seq.adjust' del v kgs

    gkgsDelete          :: EPolyHDeg p -> Op1 (GapsKerGens p)
    gkgsDelete (EPolyHDeg p hDeg)     = go      -- p in gkgs (so p /= 0, nEvGroups > 0),
                                                -- (leadEvNZ p) unique in gkgs
      where
        gap                     = if useSugar then hDeg - evTotDeg (leadEvNZ p) else 0
        go (h@(G1KGs gap0 kgs0) :! t)   = assert (gap >= gap0) $
            if gap == gap0 then G1KGs gap (kgsDelete p kgs0) :! t
            else h :! go t
        go SL.Nil               = undefined

    -- kgsReplace              :: p -> p -> Op1 (KerGens p)
    -- kgsReplace p p' kgs     = kgsInsert p' (kgsDelete p kgs)

    gkgsReplace             :: EPolyHDeg p -> EPolyHDeg p -> Op1 (GapsKerGens p)
    gkgsReplace ph ph' gkgs = gkgsInsert ph' (gkgsDelete ph gkgs)

    {-# SCC kgsFindReducer #-}
    kgsFindReducer          :: p -> KerGens p -> Maybe p
    -- returns the best (shortest) top-reducer, if any
    kgsFindReducer p kgs    =
        if pIsZero p then Nothing else
        let pEv     = leadEvNZ p
            npsF bnp                   SL.Nil                               = bnp
            npsF bnp@(SizedEPoly bn _) (ng@(SizedEPoly n ~g) :! ~t)
                | bn <= n   = bnp
                | otherwise = npsF (if evDivides (leadEvNZ g) pEv then ng else bnp) t
            esF bnp _  SL.Nil   = bnp
            esF bnp pe ((ENPs e ~nps) :! ~t)
                | pe < e    = bnp
                | otherwise = esF (npsF bnp nps) pe t
            vF bnp (pe, enpss)      = esF bnp pe enpss
            resSep  = foldl' vF (SizedEPoly (maxBound :: Int) pZero)
                        (zip (evGroup pEv) (toList kgs))
        in  if resSep.n < (maxBound :: Int) then Just resSep.p else Nothing

    gkgsFindReducer         :: p -> GapsKerGens p -> Maybe (EPolyHDeg p)
    -- returns the best (least sugar gap, then shortest) top-reducer, if any
    gkgsFindReducer p gkgs  = listToMaybe (mapMaybe find1 (toList gkgs))
      where
        find1 (G1KGs gap kgs)   =   -- if not useSugar, then h can be wrong:
            fmap (\g -> EPolyHDeg g (evTotDeg (leadEvNZ g) + gap)) (kgsFindReducer p kgs)

    gkgsReduce              :: GapsKerGens p -> Bool -> p -> (p, Int)
    -- reduce a polynomial, counting steps
    gkgsReduce gkgs doFull  = go 0
      where
        go nRedSteps p  = if pIsZero p then (p, nRedSteps) else
                            maybe go2 go1 (gkgsFindReducer p gkgs)
          where
            go1 gh  =
                let (q, r)      = topDiv p gh.p
                in  go (nRedSteps + numTerms q) r
            ~go2    = if not doFull then (p, nRedSteps) else
                let (!cd, !t)           = unconsNZ p
                    (!t', !nRedSteps')  = go nRedSteps t
                in  (cd `cons` t', nRedSteps')

    sugarReduce             :: EPolyHDeg p -> EPolyHDeg p -> (EPolyHDeg p, Int)
    sugarReduce (EPolyHDeg p pHDeg) (EPolyHDeg g gHDeg)     = (EPolyHDeg r rHDeg, nSteps)
      where
        (q, r)      = topDiv p g
        rHDeg       = if pIsZero q then pHDeg else max pHDeg (homogDeg0 q + gHDeg)
        nSteps      = numTerms q

    gkgsTopReduce           :: IO (WithNGens (GapsKerGens p)) -> EPolyHDeg p ->
                                IO (WithNGens (EPolyHDeg p), Int)
    -- top-reduce a (gh, kN)
    gkgsTopReduce kerVar    = go 0
      where
        go nRedSteps ph@(EPolyHDeg p _)     = do
            WithNGens ker nGens     <- kerVar
            let go1 gh      = do
                    let (rh, nSteps1)   = sugarReduce ph gh
                    go (nRedSteps + nSteps1) rh
            maybe (pure (WithNGens ph nGens, nRedSteps)) go1 (gkgsFindReducer p ker)

    foldReduce              :: forall f. Foldable f => f p -> p -> (Bool, p, Int)
    -- fully reduce by folding (not kgs), except stop and return True if/when a deg > 0 quotient
    foldReduce g0s          = go 0      -- all g0s /= 0, with gap 0
      where
        go nRedSteps p      = if pIsZero p then (False, p, nRedSteps) else
            let pEv     = leadEvNZ p
                mg      = find (\g -> evDivides (leadEvNZ g) pEv) g0s
                useG g  =
                    let (q, r)      = topDiv p g
                    in  if evTotDeg (leadEvNZ q) > 0 then (True, r, nRedSteps + numTerms q)
                        else go (nRedSteps + 1) r
                ~go2    =
                    let (!cd, !t)                   = unconsNZ p
                        (!todo, !t', !nRedSteps')   = go nRedSteps t
                    in  (todo, cd `cons` t', nRedSteps')
            in  maybe go2 useG mg

    foldTopReduce1          :: forall f. Foldable f => f (EPolyHDeg p) -> EPolyHDeg p ->
                                Maybe (EPolyHDeg p, Int)
    -- do 1 folding step if there's a top-reducer
    foldTopReduce1 ghs ph@(EPolyHDeg p _)   =       -- all gs /= 0
        if pIsZero p then Nothing else
        let pEv     = leadEvNZ p
            mgh     = find (\gh -> evDivides (leadEvNZ gh.p) pEv) ghs
                -- @@ improve to find best reducer!?
        in  fmap (sugarReduce ph) mgh


data StdEvCmp       = LexCmp | GrLexCmp | GrRevLexCmp   deriving (Eq, Show)
-- ^ standard monomial orders

secIsGraded         :: StdEvCmp -> Bool
secIsGraded sec     = sec /= LexCmp

-- | gbTrace bits for 'groebnerBasis' tracing. Bits 0x0F are useful to end users.
gbTSummary, gbTProgressChars, gbTProgressInfo, gbTResults, gbTQueues, gbTProgressDetails  :: Int
gbTSummary          = 0x01  -- ^ a short summary at the end of a run
gbTProgressChars    = 0x02  -- ^ total degree for each s-poly reduction result
gbTProgressInfo     = 0x04  -- ^ info when adding or removing a generator
gbTResults          = 0x08  -- ^ output final generators
gbTQueues           = 0x10  -- ^ info about threads and queues ("dprRsS", "rg")
gbTProgressDetails  = 0x20  -- ^ details relating to selection strategy

printThreadCapabilities     :: String -> [ThreadId] -> IO ()
printThreadCapabilities prefix otherThreadIds   = do
    firstThreadId       <- myThreadId
    capInfos            <- mapM threadCapability (firstThreadId : otherThreadIds)
    putStr $ prefix ++ "Threads are on capabilities: "
    mapM_ (putStrLn . unwords) (chunksOf 20 (map (show . fst) capInfos))

data GroebnerIdeal p    = GroebnerIdeal {
    gkgs        :: GapsKerGens p,
    gbGhs       :: Seq.Seq (EPolyHDeg p),   -- nonzero g's with ascending (leadEvNZ g)
    gbGens      :: Seq.Seq p,       -- a Groebner Basis
    redGbGens   :: ~(Seq.Seq p)     -- fully reduced Groebner Basis generators
}

groebnerBasis   :: forall ev term p. GBPolyOps ev term p -> Int -> Int ->
                    GroebnerIdeal p -> [p] -> IO (GroebnerIdeal p)
groebnerBasis gbpA@(GBPolyOps { .. }) nCores gbTrace gbi0 newGens   = do
    cpuTime0        <- getCPUTime
    sysTime0        <- getSystemTime
    cpuTime1Ref     <- newIORef cpuTime0
    mRTSStats0      <- getMaybeRTSStats
    let KGsOps { .. }   = kgsOps gbpA
    gkgsRef         <- newTVarIO (WithNGens gbi0.gkgs (length gbi0.gbGhs))
    genHsRef        <- newTVarIO gbi0.gbGhs :: IO (TVar (Seq.Seq (EPolyHDeg p)))
    nRedStepsRef    <- C.new (0 :: Int)
    nSPairsRedRef   <- C.new (0 :: Int)
    let _gbTQueues1 = gbTrace .&. gbTQueues /= 0 && nCores > 1
        topReduce   = gkgsTopReduce (readTVarIO gkgsRef)
        endReduce_n :: Int -> EPolyHDeg p -> IO (WithNGens (EPolyHDeg p))
        reduce2 p
            | pIsZero p     = pure pZero
            | otherwise     = do    -- fully reduce by 0 sugar gap generators
                WithNGens (g0kgs@(G1KGs 0 _) :! _) _    <- readTVarIO gkgsRef
                let (!cd, !t)       = unconsNZ p
                    (!t', !nSteps)  = gkgsReduce (SL.singleton g0kgs) True t
                when (gbTrace .&. gbTSummary /= 0) $ fetchAddInt_ nRedStepsRef nSteps
                pure (cd `cons` t')
        reduce_n gh = do        -- top reduce by all gens, then fully reduce by 0 sugar gap gens
            (WithNGens (EPolyHDeg g1 h1) kN, !nSteps)   <- topReduce gh
            when (gbTrace .&. gbTSummary /= 0) $ fetchAddInt_ nRedStepsRef nSteps
            g2                              <- reduce2 g1
            endReduce_n kN (EPolyHDeg g2 h1)
        gap0NZ (EPolyHDeg g h)  =
            if useSugar && h /= evTotDeg (leadEvNZ g) then Nothing else Just g
        endReduce_n kN gh       = do    -- result is reduced like by reduce_n
            ghs         <- readTVarIO genHsRef
            let kN'     = Seq.length ghs
            if pIsZero gh.p then pure (WithNGens gh kN')
            else if kN >= kN' then
                pure (WithNGens (EPolyHDeg (monicizeU gh.p) gh.h) kN)
            else if 3 * nEvGroups * (kN' - kN) > kN' {- @@ tune -} then reduce_n gh
            else
                let endGHs      = Seq.drop kN ghs
                    mghn        = foldTopReduce1 endGHs gh
                    endRed1 (ph, nSteps)    = do
                        when (gbTrace .&. gbTSummary /= 0) $ fetchAddInt_ nRedStepsRef nSteps
                        reduce_n ph
                    endRed2 (EPolyHDeg g h) = do
                        let g0s                     = mapMaybe gap0NZ (toList endGHs)
                            (!cd, !t)               = unconsNZ g
                            (!todo, !t', !nSteps)   = foldReduce g0s t
                        when (gbTrace .&. gbTSummary /= 0) $ fetchAddInt_ nRedStepsRef nSteps
                        p       <- (if todo then reduce2 else pure) (cd `cons` t')
                        endReduce_n kN' (EPolyHDeg p h)
                in  maybe (endRed2 gh) endRed1 mghn
        checkGkgs   = do
            ghs         <- readTVarIO genHsRef
            let n       = Seq.length ghs
                p (WithNGens _gkgs k)   = k < n
                f (WithNGens gkgs k)    = WithNGens (gkgsInsert (Seq.index ghs k) gkgs) (k + 1)
            whenM (maybeAtomicModifyTVarIO' gkgsRef p f) $ do
                traceEvent "  checkGkgs: atomic modified gkgsRef" $ pure ()
                checkGkgs
    -- rgs is a [(g, i)] of nonzero g with descending (leadEvNZ g)
    rNTraceRef      <- newIORef 0
    let rgsInsert   :: EPolyHDeg p -> Int -> [(p, Int)] -> IO [(p, Int)]
        rgsInsert (EPolyHDeg g _) i []                  = pure [(g, i)]
        rgsInsert gh@(EPolyHDeg g gHDeg) i rgs@((g1, j) : t)
            | evCmp (leadEvNZ g) (leadEvNZ g1) == GT    = pure ((g, i) : rgs)
            | evDivides (leadEvNZ g) (leadEvNZ g1)  = do
                when (gbTrace .&. gbTProgressInfo /= 0) $
                    putStrLn $ " remove g" ++ show j ++ " (" ++ pShowEV g1 ++ ") by g" ++ show i
                        ++ " (" ++ pShowEV g ++ ")"
                ghs     <- readTVarIO genHsRef
                let hh  = Seq.index ghs j
                checkGkgs
                atomically $ modifyTVar' gkgsRef (wngFirst (gkgsDelete hh))
                rgsInsert gh i t
            | otherwise                                 = do
                t'          <- rgsInsert gh i t
                if useSugar && gHDeg /= evTotDeg (leadEvNZ g) then pure ((g1, j) : t') else do
                    let (q, r)  = pR.bDiv True g1 g
                    if pIsZero q then pure ((g1, j) : t') else do
                        when (gbTrace .&. gbTSummary /= 0) $
                            fetchAddInt_ nRedStepsRef (numTerms q)
                        when (gbTrace .&. gbTQueues /= 0) $
                            if evTotDeg (leadEvNZ q) == 0 then inc rNTraceRef 1 else putChar 'R'
                        r'          <- if evTotDeg (leadEvNZ q) == 0 then pure r else reduce2 r
                        ghs0        <- readTVarIO genHsRef
                        let hh      = Seq.index ghs0 j
                            rh'     = EPolyHDeg r' hh.h
                        checkGkgs
                        atomically $ modifyTVar' gkgsRef (wngFirst (gkgsReplace hh rh'))
                        atomically $ modifyTVar' genHsRef (Seq.update j rh')
                        assert (not (pIsZero r')) (pure ((r', j) : t'))
    wakeAllThreads  <- newTVarIO 0          :: IO (TVar Int)
    wakeMainThread  <- newTVarIO 0          :: IO (TVar Int)
    gDShownRef      <- newIORef 0           :: IO (IORef Word)
    let putS        = if gbTrace .&. gbTProgressChars /= 0 then hPutStr stderr else putStr
    let addGenHN (WithNGens gh kN)  = {-# SCC addGenHN #-}
            unless (pIsZero gh.p) $ do
                traceEvent "  addGenHN start" $ pure ()
                kNIsLow     <- atomically $ do
                    ghs         <- readTVar genHsRef
                    let res     = Seq.length ghs > kN
                    unless res $ writeTVar genHsRef $! ghs Seq.|> gh
                    pure res
                if kNIsLow then addGenHN =<< endReduce_n kN gh else do
                    inc1TVar wakeAllThreads
                    let p (WithNGens _gkgs k)   = k == kN
                        f (WithNGens gkgs k)    = WithNGens (gkgsInsert gh gkgs) (k + 1)
                    whenM (maybeAtomicModifyTVarIO' gkgsRef p f) $ do
                        traceEvent "  atomic modified gkgsRef" $ pure ()
                        checkGkgs
                    when (gbTrace .&. (gbTQueues .|. gbTProgressChars) /= 0) $ do
                        putS "d"
                        let d       = evTotDeg (leadEvNZ gh.p)
                        gDShown     <- readIORef gDShownRef
                        when (d /= gDShown) $ do
                            putS $ show d ++ " "
                            writeIORef gDShownRef d
                    traceEvent ("  addGenHN end " ++ show kN) $ pure ()
    gMGisRef        <- newTVarIO (fmap (Just . giNew gbpA) gbi0.gbGhs)
                                        :: IO (TVar (Seq.Seq (Maybe (GBGenInfo ev))))
    ijcsRef         <- newTVarIO SL.Nil :: IO (TVar (SortedSPairs ev))  -- ascending by hEvCmp
    let newIJCs     = do
            ghs0        <- readTVarIO genHsRef
            gMGis00     <- readTVarIO gMGisRef  -- for speed, to avoid atomic transaction
            if Seq.length gMGis00 >= Seq.length ghs0 then pure False else do
                ijcs0       <- readTVarIO ijcsRef
                mx          <- atomically $ do
                    gMGis       <- readTVar gMGisRef
                    if Seq.length gMGis >= Seq.length ghs0 then pure Nothing else do
                        let t       = Seq.length gMGis
                            gh      = Seq.index ghs0 t
                            tGi     = giNew gbpA gh
                        traceEvent ("  newIJCs start " ++ show t) $ pure ()
                        writeTVar gMGisRef $! gMGis Seq.|> Just tGi
                        pure (Just (gMGis, t, gh, tGi))
                case mx of
                    Nothing                     -> pure False
                    Just (!gMGis0, !t, !gh, !tGi)       -> do
                        let (skipIs, skipIJCs, addITCs)     =
                                updatePairs gbpA (toList gMGis0) ijcs0 tGi
                            skipIF s i  = Seq.update i Nothing s
                        {-
                            toIJ (SPair i j _ _)    = (i, j)
                            toIJs ijms              = map toIJ (toList ijms)
                        traceEvent ("  updatePairs result: "
                            ++ show (t, skipIs, toIJs skipIJCs, toIJs addITCs)) $ pure ()
                        -}
                        unless (null skipIs) $      -- 'unless' for speed
                            atomically $ modifyTVar' gMGisRef (\ms -> foldl' skipIF ms skipIs)
                        ijcs        <- atomically $ do
                            ijcs        <- readTVar ijcsRef
                            writeTVar ijcsRef $! SL.minusSorted hEvCmp ijcs skipIJCs
                            pure ijcs
                        ijcs'       <- atomically $ do
                            ijcs1       <- readTVar ijcsRef
                            let ijcs'   = SL.mergeBy hEvCmp ijcs1 addITCs
                            writeTVar ijcsRef ijcs'
                            pure ijcs'
                        when (SL.null ijcs && not (SL.null ijcs')) $ inc1TVar wakeAllThreads
                        when (gbTrace .&. gbTQueues /= 0) $ do
                            let n       = length ijcs
                                n'      = length ijcs'
                            when (n' < n || n' > n + 10) $
                                putStr $ 'p' : show n ++ "-" ++ show n' ++ " "
                            when ((t + 1) `rem` 50 == 0) $
                                putStr $ 'p' : show (t + 1) ++ ":" ++ show n' ++ " "
                        when (gbTrace .&. gbTProgressInfo /= 0) $
                            putStrLn $ " g" ++ show t ++ ": " ++ pShowEV gh.p
                        traceEvent ("  newIJCs done " ++ show t) $ pure True
        rgs0        = reverse (zipWith (\gh i -> (gh.p, i)) (toList gbi0.gbGhs) [0 ..])
    rgsRef          <- newIORef rgs0                            :: IO (IORef [(p, Int)])
    rgsMNGensRef    <- newIORef (Just (length gbi0.gbGens))     :: IO (IORef (Maybe Int))
        -- Nothing if locked
    let checkRgs1   = do    -- may add 1 gh to rgs
            mk          <- readIORef rgsMNGensRef   -- for speed, to avoid atomic modify
            case mk of
                Just k      -> do
                    ghs         <- readTVarIO genHsRef
                    if k < Seq.length ghs then do
                        let f mk1   = if mk1 == mk then (Nothing, True) else (mk1, False)
                        res         <- atomicModifyIORef' rgsMNGensRef f
                        when res $ do
                            rgs         <- readIORef rgsRef
                            let gh      = Seq.index ghs k
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
        newG sp@(SPair i j h c)     = {-# SCC newG #-} do
            let ~s  = " start spair(g" ++ show i ++ ",g" ++ show j ++ "): sugar degree " ++
                        show h ++ ", lcm of heads " ++ evShow c
            when (gbTrace .&. gbTProgressDetails /= 0) $ putStrLn s
            traceEvent ("  newG" ++ show (i, j)) $ pure ()
            when (gbTrace .&. gbTSummary /= 0) $ fetchAddInt_ nSPairsRedRef 1
            ghs     <- readTVarIO genHsRef
            let f   = if i < 0 then pZero else (Seq.index ghs i).p
            ghn     <- reduce_n (EPolyHDeg (sPoly f (Seq.index ghs j).p sp) h)
            addGenHN ghn
            pure True
        doSP        = maybe (pure False) newG =<< slPop ijcsRef
    numSleepingRef      <- newIORef 0       :: IO (IORef Int)   -- not counting main thread
    let checkQueues t   = do
            loop
          where
            tasks       = [checkRgs1 | t == 1] ++   -- @@ tune:
                if      3 * t < nCores then [newIJCs, doSP]
                else                        [doSP, newIJCs]
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
    mapM_ (\g -> addGenHN =<< reduce_n (EPolyHDeg g (homogDeg0 g)))
        (sortBy (evCmp `on` leadEvNZ) (filter (not . pIsZero) newGens))
    auxThreadIds        <- forM [1 .. nCores - 1] (\t -> forkOn t (checkQueues t))
    let traceTime   = do
            cpuTime2        <- getCPUTime
            cpuTime1        <- readIORef cpuTime1Ref
            when (cpuTime2 - cpuTime1 > 1_000_000_000_000) $ do
                s               <- cpuElapsedStr cpuTime0 sysTime0 mRTSStats0
                putStr $ ' ' : s ++ ": "
                writeIORef cpuTime1Ref cpuTime2
                numSleeping <- readIORef numSleepingRef
                ghs         <- readTVarIO genHsRef
                WithNGens _gkgs kN  <- readTVarIO gkgsRef
                rgsMNGHs    <- readIORef rgsMNGensRef
                rgs         <- readIORef rgsRef
                gMGis       <- readTVarIO gMGisRef
                ijcs        <- readTVarIO ijcsRef
                putStrLn $
                    show (Seq.length ghs) ++ " gens, " ++
                    show kN ++ " gkg'd, " ++
                    maybe "busy" show rgsMNGHs ++ " rg'd, " ++
                    show (length rgs) ++ " rgs, " ++    -- omit?
                    show (Seq.length gMGis) ++ " paired, " ++
                    show (length ijcs) ++ " pairs" ++
                    if numSleeping > 0 then ", " ++ show numSleeping ++ " sleeping" else ""
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
        orM [newIJCs, checkRgs1, doSP, doSleep]
    when (gbTrace .&. (gbTQueues .|. gbTProgressChars) /= 0) $ putS "\n"
    when (gbTrace .&. gbTSummary /= 0) $ printThreadCapabilities " " auxThreadIds
    mapM_ killThread auxThreadIds
    when (gbTrace .&. gbTSummary /= 0) $ do
        t           <- cpuElapsedStr cpuTime0 sysTime0 mRTSStats0
        putStrLn $ "Groebner Basis CPU/Elapsed Times: " ++ t
        nSPairsRed  <- C.get nSPairsRedRef
        putStrLn $ "# SPairs reduced = " ++ show nSPairsRed
        nRedSteps   <- C.get nRedStepsRef
        putStrLn $ "# reduction steps (quotient terms) = " ++ show nRedSteps
            -- Macaulay just counts top-reduced
        ghs         <- readTVarIO genHsRef
        let ndhs    = [(numTerms g, evTotDeg (leadEvNZ g), h) | EPolyHDeg g h <- toList ghs]
        putStrLn $ "generated (redundant) basis has " ++ show (Seq.length ghs) ++
            " elements with " ++ show (sum (map fst3 ndhs)) ++ " monomials"
        when (gbTrace .&. gbTProgressDetails /= 0) $ do
            putStrLn "(whether used & head degree + sugar, # monomials):"
            let show4 (n, d, h) m   =
                    let dh  = h - d
                    in  maybe "x" (const "") m ++ show d ++
                            (if dh > 0 then '+' : show dh else "") ++ "," ++ show n
            gMGisL      <- toList <$> readTVarIO gMGisRef
            mapM_ (putStrLn . unwords) (chunksOf 10 (zipWith show4 ndhs gMGisL))
    rgs1        <- readIORef rgsRef
    ghs1        <- readTVarIO genHsRef
    let gbGhs   = Seq.fromList (map (Seq.index ghs1 . snd) (reverse rgs1))
        gbGens  = fmap (.p) gbGhs
        ~s      = show (length gbGens) ++ " generators"
    if gbTrace .&. gbTResults /= 0 then do
        putStrLn (s ++ ":")
        mapM_ (putStrLn . pShow) gbGens
    else when (gbTrace .&. gbTSummary /= 0) $ putStrLn s
    {- when (gbTrace .&. gbTQueues /= 0) $ do
        hFlush stdout
        callCommand "echo; ps -v" -}
    WithNGens gkgs _kN  <- readTVarIO gkgsRef
    let fullReduce2NZ p     = cd `cons` fst (gkgsReduce gkgs True t)
          where
            (!cd, !t)   = unconsNZ p
        ~redGbGens  =   if not useSugar then gbGens else
            Seq.fromList (fmap fullReduce2NZ (toList gbGens) `using` parListChunk 10 rseq)
    pure $ GroebnerIdeal { gkgs, gbGhs, gbGens, redGbGens }
  where
    pZero           = pR.zero
    pIsZero         = pR.isZero
    evShow          = evShowPrec 0
    pShowEV p
        | pIsZero p         = "0"
        | numTerms p < 10   = pShow (monicizeU p)
        | otherwise         = evShow (leadEvNZ p) ++ "+... (" ++ show (numTerms p) ++ " terms)"
    hEvCmp          = spCmp evCmp useSugar      :: Cmp (SPair ev)


gbiSmOps        :: GBPolyOps ev term p -> Int -> SubmoduleOps p p (GroebnerIdeal p)
-- ^ @gbiSmOps gbpA nCores@
gbiSmOps gbpA nCores    = SubmoduleOps { .. }
  where
    KGsOps { gkgsEmpty, gkgsReduce }    = kgsOps gbpA
    zeroMd  = GroebnerIdeal gkgsEmpty Seq.empty Seq.empty Seq.empty
    plusGens gbTrace gbi0 newGens   =
        unsafePerformIO $ groebnerBasis gbpA nCores gbTrace gbi0 newGens
    stdGens doFullReduce gbi    = if doFullReduce then gbi.redGbGens else gbi.gbGens
    bModBy doFullReduce gbi p   = fst (gkgsReduce gbi.gkgs doFullReduce p)