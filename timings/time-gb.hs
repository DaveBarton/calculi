import Math.Algebra.Commutative.GBDemo

import Data.List (isInfixOf)

import Control.Concurrent (forkOn, getNumCapabilities)
import Control.Concurrent.MVar (newEmptyMVar, putMVar, takeMVar)
import GHC.Conc (getNumProcessors)

import Data.Time.Clock (getCurrentTime)
import Data.Time.LocalTime (getCurrentTimeZone, localDay, utcToLocalTime)

import Data.Version (showVersion)
import System.Info (arch, compilerName, os)
import System.Info (fullCompilerVersion)

import Control.Exception (SomeException, try)
import Control.Monad (void, when)
import System.IO (hFlush, stderr, stdout)
import System.Process (callCommand)


isLinux         :: Bool
isLinux         = "linux" `isInfixOf` os

main    :: IO ()
main    = do
    let tryCommand s    = void $ try @SomeException $ callCommand s
    tryCommand "uptime"
    if isLinux then
        tryCommand "echo; lscpu; echo; numactl --hardware; echo; numactl --show"
    else
        tryCommand "sysctl hw.physicalcpu"
    
    nCores      <- getNumCapabilities
    
    now         <- getCurrentTime
    tz          <- getCurrentTimeZone
    let today       = localDay (utcToLocalTime tz now)
    maxNCores   <- getNumProcessors
    putStrLn $ "\n" ++ show today ++ ", " ++ arch ++ "-" ++ os ++ "/" ++ compilerName ++ "-"
        ++ showVersion fullCompilerVersion
        ++ ", using " ++ show nCores ++ " of " ++ show maxNCores ++ " cores\n"
    
    doneMVar    <- newEmptyMVar
    _           <- forkOn 0 $ do
        -- for gbTrace bits, see Math/Algebra/Commutative/GroebnerBasis.hs:
        let gbTrace     = gbTSummary -- @@@ .|. gbTQueues
        mapM_ (\ex -> ex nCores gbTrace) [katsura8, cyclic7, jason210]
        hFlush stdout
        hFlush stderr
        putMVar doneMVar ()
    takeMVar doneMVar
    
    when isLinux $ tryCommand "echo; numastat $PPID"
