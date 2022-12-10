{-# LANGUAGE CPP #-}

import Math.Algebra.Commutative.GBDemo

import Data.List (isInfixOf)

import Control.Concurrent (forkOn, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import GHC.Conc (getNumProcessors)

import Data.Time.Clock (getCurrentTime)
import Data.Time.LocalTime (getCurrentTimeZone, localDay, utcToLocalTime)

import Data.Version (showVersion)
import System.Info (arch, compilerName, os)
#if MIN_VERSION_base(4,15,0)
import System.Info (fullCompilerVersion)    -- ghc >= 9.0.1
#else
import System.Info (compilerVersion)
#endif

import Control.Exception (SomeException, try)
import Control.Monad (void, when)
import System.IO (hFlush, stdout)
import System.Process (callCommand)


isLinux         :: Bool
isLinux         = "linux" `isInfixOf` os

main    :: IO ()
main    = do
    let tryCommand s    = void $ try @SomeException $ callCommand s
    tryCommand "uptime"
    if isLinux then
        tryCommand "lscpu; numactl --hardware; echo; numactl --show"
    else
        tryCommand "sysctl hw.physicalcpu"
    
    nCores      <- getNumCapabilities
    
    now         <- getCurrentTime
    tz          <- getCurrentTimeZone
    let today       = localDay (utcToLocalTime tz now)
    maxNCores   <- getNumProcessors
    putStrLn $ "\n" ++ show today ++ ", " ++ arch ++ "-" ++ os ++ "/" ++ compilerName ++ "-"
        ++ showVersion
#if MIN_VERSION_base(4,15,0)
            fullCompilerVersion
#else
            compilerVersion
#endif
        ++ ", using " ++ show nCores ++ " of " ++ show maxNCores ++ " cores\n"
    
    doneMVar    <- newEmptyMVar
    _           <- forkOn 0 $ do
        -- for gbTrace bits, see Math/Algebra/Commutative/GroebnerBasis.hs:
        let gbTrace     = gbTSummary .|. gbTQueues
        mapM_ (\ex -> ex nCores gbTrace) [katsura8, cyclic7, jason210]
        hFlush stdout
        putMVar doneMVar ()
    takeMVar doneMVar
    
    when isLinux $ tryCommand "echo; numastat $PPID"
