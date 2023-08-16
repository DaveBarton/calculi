import Math.Algebra.Commutative.GroebnerBasis (runOn0)
import Math.Algebra.Commutative.GBDemo

-- import Data.List (isInfixOf)

import Control.Concurrent (getNumCapabilities)
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


-- isLinux         :: Bool
-- isLinux         = "linux" `isInfixOf` os

main    :: IO ()
main    = do
    nCores      <- getNumCapabilities
    args        <- getArgs
    
    now         <- getCurrentTime
    tz          <- getCurrentTimeZone
    let today       = localDay (utcToLocalTime tz now)
    maxNCores   <- getNumProcessors
    putStrLn $ "\n" ++ show today ++ ", " ++ arch ++ "-" ++ os ++ "/" ++ compilerName ++ "-"
        ++ showVersion fullCompilerVersion
        ++ ", using " ++ show nCores ++ " of " ++ show maxNCores ++ " cores\n"
    
    runOn0 $ gbDemo nCores args
    -- hFlush stdout
    -- hFlush stderr
    
    -- let tryCommand s    = void $ try @SomeException $ callCommand s
    -- when isLinux $ tryCommand "numastat $PPID; echo"
