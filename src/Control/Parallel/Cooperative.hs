{-# LANGUAGE Strict #-}

{- |  This module supports cooperative parallelism, where a task can know what, and how much,
    other tasks have computed so far. This can enable or greatly speed up non-\"obviously\"
    parallel algorithms. Note that this can introduce nondeterminism as tasks vary speeds over
    different runs, unlike (say) GHC's sparks. The programmer should ensure final results are
    deterministic (unique) when feasible.
    
    In this module, a @task@ is an action that looks for a computation to perform. If it finds
    one, the task does it and returns @True@; else the task returns @False@. Different tasks are
    typically combined using 'Control.Monad.Extra.orM', and then these composite tasks are run
    in separate threads. If a thread has nothing to do, it \"sleeps\" (blocks in an @STM@
    transaction), though it can be woken up later. When all threads are done, the last one awake
    returns and the parent algorithm terminates.
    
    We recommend the threads communicate their shared state (results so far) using a small
    number of software transactional memory (STM) @TVar@s, each holding a purely strict data
    structure (no thunks). Then threads can read each others' latest results using
    'Control.Concurrent.STM.TVar.readTVarIO' without ever blocking, even with many cores and
    significant contention (unlike with an @IORef@ or @MVar@).
    
    If you can guarantee your threads never block during a task, you can allocate them
    one-per-core (really one-per-capability) using 'parNonBlocking', for a small performance
    speedup. Otherwise, it's better to have some extra threads, and let them migrate between
    cores, using 'parThreads'. In either case, we don't create and destroy threads as often as
    sparks do, which seems to speed things up.
    
    This module uses "Control.Concurrent.Async" to ensure that uncaught exceptions are
    propagated to parent threads, and orphaned threads are always killed.
    
    You may want or need to put a line in your @cabal@ file like:
    
    @ghc-options: -threaded -rtsopts \"-with-rtsopts=-N -A64m -s\"@
    
    More precisely, we've found a @-A@ value of about 2MB per core works well. More information
    on these options is in the GHC User's Guide.
-}

module Control.Parallel.Cooperative (
    -- * Cooperative parallelism
    parThreads, parNonBlocking,
    
    -- * Simple (non-cooperative) parallelism
    evalPar, forkJoinPar, mapParChunk, fmapParChunk, seqMapParChunk, imsMapParChunkTo,
    vecMapParChunk, rrbMapParChunk,
    
    -- * Folding and sorting
    foldBalanced, foldBalancedPar, sortLBy, -- sortByPar,
    
    -- * Utilities
    seqSpine, seqElts, inc1TVar, maybeStateTVar, popTVar,
    lowNzBit, fbTruncLog2, floorLogBase,
    getSystemTimeNS
) where

import Control.Monad (when)
import Control.Monad.Extra (ifM, unlessM, whileM)
import Control.Monad.ST (runST)
import Data.Bits (Bits, FiniteBits, (.&.), bit, countLeadingZeros, finiteBitSize, xor)
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IMS
import Data.List (uncons, unfoldr)
import Data.List.Extra (chunksOf)
-- import Data.Maybe (isJust)
import Data.Maybe (isNothing)
import Data.Primitive.Array (pattern MutableArray)
import qualified Data.Primitive.Contiguous as C
import qualified Data.RRBVector as RRB
import Data.SamSort (sortArrayBy)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import GHC.Stack (HasCallStack)

import Control.Concurrent (getNumCapabilities, myThreadId, threadCapability)
import Control.Concurrent.Async (Async, wait, withAsync, withAsyncOn)
import Control.Concurrent.STM.TVar (TVar, modifyTVar', newTVarIO, readTVar, readTVarIO,
    stateTVar, writeTVar)
import Control.Monad.STM (STM, atomically, retry)
import System.IO.Unsafe (unsafePerformIO)

import Data.Time.Clock.System (SystemTime(MkSystemTime), getSystemTime)
import qualified Debug.TimeStats as TS
-- import Numeric (showFFloatAlt)


-- * Utilities

seqSpine        :: Foldable t => t a -> t a
-- ^ Evaluate the spine of a structure, and return it.
seqSpine xs     = foldr (\ _ y -> y) xs xs

seqElts         :: Foldable t => t a -> t a
-- ^ @seq@ all elements of a structure, and return it.
seqElts xs      = foldr seq xs xs

inc1TVar        :: TVar Int -> IO ()
-- ^ Atomically add 1 to a @TVar@.
inc1TVar var    = atomically $ modifyTVar' var (+ 1)

maybeStateTVar  :: TVar s -> (s -> Maybe (a, s)) -> STM (Maybe a)
-- ^ E.g., try to remove an element using an @uncons@ function.
maybeStateTVar var f    = stateTVar var f'
  where
    f' s    = case f s of
        Nothing         -> (Nothing, s)
        Just (a, s')    -> (Just a, s')

popTVar             :: TVar [e] -> IO (Maybe e)
-- ^ If the list is nonempty, remove and return its first element.
popTVar esTVar      = atomically $ maybeStateTVar esTVar uncons


lowNzBit        :: (Bits a, Num a) => a -> a
-- ^ The lowest nonzero bit if any, else 0.
lowNzBit n      = n .&. (- n)

fbTruncLog2     :: FiniteBits a => a -> Int
-- ^ Floor of log base 2. Let's leave this undefined if the input is 0.
fbTruncLog2 n   = finiteBitSize n - 1 - countLeadingZeros n

floorLogBase    :: Int -> Double -> Int
-- ^ @floorLogBase r maxNum = floor (logBase (fromIntegral r) maxNum)@
floorLogBase r maxNum   = floor (logBase (fromIntegral r) maxNum)


getSystemTimeNS     :: IO Integer
-- ^ 'Data.Time.Clock.System.getSystemTime' in nanoseconds, e.g. for logging times.
getSystemTimeNS     = do
    MkSystemTime s ns   <- getSystemTime
    pure $ 1_000_000_000 * toInteger s + toInteger ns


-- * Cooperative parallelism

type WithAsyncF     = IO () -> (Async () -> IO ()) -> IO ()     -- returned by withAsync[On]
parWithAsyncs   :: TVar Int -> TVar Int -> [(WithAsyncF, IO Bool)] -> IO ()
parWithAsyncs wakeAllThreads numSleepingVar allPairs    = do
    atomically $ writeTVar wakeAllThreads 0
    atomically $ writeTVar numSleepingVar 0
    case allPairs of
        []              -> pure ()
        [(_, task)]     -> whileM task
        _               -> go [] allPairs
  where
    numThreads      = length allPairs
    go asyncs []                    = mapM_ wait (reverse asyncs)
    go asyncs ((waf, task) : ps)    = waf threadF (\aa -> go (aa : asyncs) ps)
      where
        done        = (== numThreads) <$> readTVarIO numSleepingVar
        threadF     = do
            wake0       <- readTVarIO wakeAllThreads
            q           <- task
            if q then threadF else do
                inc1TVar numSleepingVar
                ifM done (inc1TVar wakeAllThreads) $ do
                    TS.measureM "sleep" $ atomically $ do
                        wake1       <- readTVar wakeAllThreads
                        when (wake1 == wake0) retry
                    unlessM done $ do
                        atomically $ modifyTVar' numSleepingVar (subtract 1)
                        threadF

parThreads      :: TVar Int -> TVar Int -> [IO Bool] -> IO ()
{- ^ @parThreads wakeAllThreads numSleepingVar tasks@ runs the @tasks@ in separate threads. When
	a task returns False, its thread \"sleeps\" (blocks on @wakeAllThreads@). When all threads
	are sleeping, @parThreads@ returns. @inc1TVar wakeAllThreads@ wakes all sleeping threads.
	@readTVarIO numSleepingVar@ gives the number of currently sleeping threads, for instance for
	log messages. If you can guarantee the threads never block during a task, 'parNonBlocking'
	may be somewhat faster. -}
parThreads wakeAllThreads numSleepingVar tasks  =
    parWithAsyncs wakeAllThreads numSleepingVar (map (withAsync, ) tasks)

parNonBlocking  :: TVar Int -> TVar Int -> (Int -> Int -> IO Bool) -> IO ()
{- ^ @parNonBlocking wakeAllThreads numSleepingVar taskF@ is similar to 'parThreads', but runs
	the threads on separate capabilities (cores), using tasks @taskF numCaps capIndex@. -}
parNonBlocking wakeAllThreads numSleepingVar taskF  = do
    numCaps         <- getNumCapabilities
    (cap, _)        <- myThreadId >>= threadCapability
    parWithAsyncs wakeAllThreads numSleepingVar
        [(withAsyncOn (cap + i), taskF numCaps i) | i <- [1 .. numCaps - 1] ++ [0]]


-- * Simple (non-cooperative) parallelism

evalPar         :: [a] -> [a]
{- ^ Use 'parNonBlocking' to evaluate each list element in parallel. This is similar to
    @seqElts . (\`using\` parList rseq)@ from "Control.Parallel.Strategies", but may be somewhat
    faster. Normally the input list has been \"chunked\" from a larger list or computation.
    If the chunking function is lazy, it'll be parallelized also. -}
evalPar es      = if null (drop 1 es) then seqElts es else
    unsafePerformIO $ do  -- no side effects escape, so 'unsafePerformIO' is safe
        -- start           <- getSystemTimeNS
        wakeAllThreads  <- newTVarIO 0
        numSleepingVar  <- newTVarIO 0
        todo            <- newTVarIO es
        let taskF _numCaps _capIndex    = do
                me      <- popTVar todo
                {- now     <- getSystemTimeNS
                putStrLn $ "evalPar - capIndex " <> show _capIndex <> ", "
                    <> showFFloatAlt (Just 3) (1e-9 * fromInteger (now - start) :: Double) "s: "
                    <> show (isJust me) -}
                pure (maybe False (`seq` True) me)
        parNonBlocking wakeAllThreads numSleepingVar taskF
        pure es

forkJoinPar     :: (a -> [b]) -> ([c] -> d) -> (b -> c) -> a -> d
{- ^ Use 'parNonBlocking' to compute a function in parallel over chunks. If the splitting
    function is lazy, it'll be parallelized also. -}
forkJoinPar split join f a  = join $ evalPar (map f (split a))

checkChunkSize  :: HasCallStack => Int -> a -> a
checkChunkSize d    = if d < 1 then error ("Bad chunksize: " <> show d) else id

mapParChunk     :: HasCallStack => Int -> (a -> b) -> [a] -> [b]
{- ^ Map a function down a list, processing chunks in parallel. The chunk size must be
    positive. This is similar to @seqElts (map f es \`using\` parListChunk chunkSize rseq)@
    from "Control.Parallel.Strategies", but may be somewhat faster. -}
mapParChunk chunkSize f es  = checkChunkSize chunkSize $
    seqSpine $ concat $ evalPar (map seqElts (chunksOf chunkSize (map f es)))
{-- We map f lazily down es, instead of down each chunk, in case es' elements start out lazy
    and therefore small, and f shrinks its (evaluated/expanded) argument a lot. In that case,
    chunks filled with large intermediate values can cause extra garbage collection. (I'm not
    sure this happens in real cases, not just simple artificial benchmarks, such as
    print @Int $ sum $ mapParChunk 1000 sum $ [[1 - n .. n] | n <- [1 .. 10000]].) --}

fmapParChunk    :: (Functor t, Foldable t, Monoid (t b), HasCallStack) =>
                    (t a -> [t a]) -> (a -> b) -> t a -> t b
{- ^ Map a function down a structure, processing chunks in parallel. If the splitting
    function is lazy, it'll be parallelized also, but note 'mconcat' usually is not. -}
fmapParChunk split f    = forkJoinPar split mconcat (seqElts . fmap f)
-- Note fmap may not be lazy, so we don't want to compute (fmap f es) outside evalPar.

seqMapParChunk  :: HasCallStack => Int -> (a -> b) -> Seq.Seq a -> Seq.Seq b
{- ^ Map a function down a sequence, processing chunks in parallel. The chunk size must be
    positive. -}
seqMapParChunk chunkSize f  = checkChunkSize chunkSize $
    seqSpine . fmapParChunk (toList . Seq.chunksOf chunkSize) f

imsMapParChunkTo    :: Int -> (a -> b) -> IMS.IntMap a -> IMS.IntMap b
{- ^ Map a function down a strict IntMap, processing chunks in parallel, up to a chunk depth. -}
imsMapParChunkTo    = fmapParChunk . chunksTo
  where
    chunksTo depth ims
        | depth < 1     = [ims]
        | otherwise     = concatMap (chunksTo (depth - 1)) (IMS.splitRoot ims)

vecChunksOf     :: HasCallStack => Int -> V.Vector a -> [V.Vector a]
{- ^ Split a vector into chunks of a given size, possibly with a smaller but nonempty final 
    chunk. The given chunk size must be positive. -}
vecChunksOf chunkSize   = checkChunkSize chunkSize $ unfoldr go
  where
    go v    = if null v then Nothing else Just (V.splitAt chunkSize v)

vecMapParChunk  :: HasCallStack => Int -> (a -> b) -> V.Vector a -> V.Vector b
{- ^ Map a function over a vector, processing chunks in parallel. The chunk size must be
    positive. -}
vecMapParChunk d    = fmapParChunk (vecChunksOf d)

rrbChunksOf     :: HasCallStack => Int -> RRB.Vector a -> [RRB.Vector a]
{- ^ Split a vector into chunks of a given size, possibly with a smaller but nonempty final 
    chunk. The given chunk size must be positive. -}
rrbChunksOf chunkSize   = checkChunkSize chunkSize $ unfoldr go
  where
    go v    = if null v then Nothing else Just (RRB.splitAt chunkSize v)

rrbMapParChunk  :: HasCallStack => Int -> (a -> b) -> RRB.Vector a -> RRB.Vector b
{- ^ Map a function over an RRB vector, processing chunks in parallel. The chunk size must be
    positive. -}
rrbMapParChunk chunkSize    = fmapParChunk (rrbChunksOf chunkSize)

{- Scala's parallel collections split RRBVectors (and other collections) roughly in half, sort
    of like IntMap's @splitRoot@, instead of using a @chunkSize@. -}


-- * Folding and sorting

foldPairs       :: (a -> a -> a) -> [a] -> [a]
foldPairs  f (a : b : c)    = f a b : foldPairs f c
foldPairs _f as01           = as01

foldBalanced    :: (a -> a -> a) -> [a] -> a
{- ^ Fold an operation over a nonempty list, with a balanced call tree. Note this can build up
    a tree of thunks while it's working, even if f is strict. -}
foldBalanced _f [a]     = a
foldBalanced _f []      = undefined
foldBalanced  f as      = foldBalanced f (foldPairs f as)

foldBalancedPar :: (a -> a -> a) -> [a] -> a
{- ^ 'foldBalanced' in parallel, using 'parNonBlocking'. Normally the input list has been
    \"chunked\" from a larger list or computation, and it must be nonempty. -}
foldBalancedPar f as    = if null (drop 3 as) then foldBalanced f as else
    unsafePerformIO $ do  -- no side effects escape this 'unsafePerformIO'
        wakeAllThreads  <- newTVarIO 0
        numSleepingVar  <- newTVarIO 0
        doneVar         <- newTVarIO IMS.empty
        todo            <- newTVarIO (zip [1, 3 ..] (foldPairs f as))
        let taskF _numCaps _capIndex    = do
                me      <- popTVar todo
                case me of
                    Nothing         -> pure False
                    Just (k, a)     -> go k a
            go k a      = if kParent >= n && k /= top then go kParent a else do
                mb          <- atomically $ do
                    me          <- stateTVar doneVar
                                    (IMS.updateLookupWithKey (\_ _ -> Nothing) kb)
                    when (isNothing me) $ modifyTVar' doneVar (IMS.insert k a)
                    pure me
                maybe (pure True) (go kParent . f a) mb
              where
                kb          = buddy k
                kParent     = (k + kb) `div` 2
        parNonBlocking wakeAllThreads numSleepingVar taskF
        done            <- readTVarIO doneVar
        pure (done IMS.! top)
      where
        {- We number the tree of calls of f, expanded to a full binary tree, using inorder
            traversal, starting at 1. Thus row `i` from the bottom contains the nodes whose
            corresponding number has `i` trailing zeros. -}
        n               = length as
        buddy k         = (2 * lowNzBit k) `xor` k
        top             = bit (fbTruncLog2 n)

sortLBy         :: (a -> a -> Ordering) -> [a] -> [a]
{- ^ Like 'Data.List.sortBy', but faster, though not lazy (it always sorts the entire list).
    'sortLBy' currently uses [samsort](https://hackage.haskell.org/package/samsort), so it's
    stable and adaptive. Also like 'Data.SamSort.sortArrayBy', 'sortLBy' will inline to get the
    best performance out of statically known comparison functions. To avoid code duplication,
    create a wrapping definition and reuse it as necessary. -}
sortLBy cmp xs  = runST $ do
    ma@(MutableArray ma')   <- C.fromListMutable xs
    n                       <- C.sizeMut ma
    sortArrayBy cmp ma' 0 n
    C.toListMutable ma
{-# INLINE sortLBy #-}

{- @@@ faster to just use sortLBy (samsort)
sortByPar   :: Int -> (a -> a -> Ordering) -> [a] -> [a]
{- ^ Strict stable sort by sorting chunks in parallel. The chunk size must be positive, and 100
    appears to be a good value. The spine of the result is forced. -}
sortByPar chunkSize cmp as  = if null as then [] else
    forkJoinPar (chunksOf chunkSize) (foldBalancedPar (\es -> seqSpine . mergeBy cmp es))
        (seqSpine . sortLBy cmp) as
-- @@@ INLINE sortByPar also, doc
-}
