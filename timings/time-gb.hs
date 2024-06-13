import Math.Algebra.Commutative.GBDemo

-- import Data.List (isInfixOf)
import Fmt ((+|), (|+), (+||), (||+), fmtLn)

import Control.Concurrent (getNumCapabilities, runInUnboundThread)
import GHC.Conc (getNumProcessors)

import Data.Time.Clock (getCurrentTime)
import Data.Time.LocalTime (getCurrentTimeZone, localDay, utcToLocalTime)

import Data.Version (showVersion)
import System.Environment (getArgs)
import System.Info (arch, compilerName, os)
import System.Info (fullCompilerVersion)

-- import Control.Exception (SomeException, try)
-- import Control.Monad (void, when)
-- import System.IO (hFlush, stderr, stdout)
-- import System.Process (callCommand)

{- import Control.Parallel.Cooperative
import System.Random
import Data.List (unfoldr) -}


-- isLinux         :: Bool
-- isLinux         = "linux" `isInfixOf` os

main    :: IO ()
main    = do
{-    let rands   = take 300000 $ unfoldr (Just . uniform) (mkStdGen 137) :: [Int]
    print $ sum $ sortByPar 100 compare rands -}
    
    nCores      <- getNumCapabilities
    args        <- getArgs
    
    now         <- getCurrentTime
    tz          <- getCurrentTimeZone
    let today       = localDay (utcToLocalTime tz now)
    maxNCores   <- getNumProcessors
    fmtLn $ "\n"+||today||+", "+|arch|+"-"+|os|+"/"
        +|compilerName|+"-"+|showVersion fullCompilerVersion|+
        ", using "+|nCores|+" of "+|maxNCores|+" cores\n"
    runInUnboundThread $ gbDemo args
    -- hFlush stdout
    -- hFlush stderr
    
    -- let tryCommand s    = void $ try @SomeException $ callCommand s
    -- when isLinux $ tryCommand "numastat $PPID; echo"
