import Math.Algebra.Commutative.GBDemo

import Control.Concurrent (getNumCapabilities, runInUnboundThread)
import GHC.Conc (getNumProcessors)

import Data.Time.Clock (getCurrentTime)
import Data.Time.LocalTime (getCurrentTimeZone, localDay, utcToLocalTime)

import Data.Version (showVersion)
import System.Info (arch, compilerName, compilerVersion, os)
    -- @@@ change compilerVersion to fullCompilerVersion for ghc >= 9.0.1, base >= 4.15


main    :: IO ()
main    = do
    nCores      <- getNumCapabilities
    
    now         <- getCurrentTime
    tz          <- getCurrentTimeZone
    let today       = localDay (utcToLocalTime tz now)
    maxNCores   <- getNumProcessors
    putStrLn $ "\n" ++ show today ++ ", " ++ arch ++ "-" ++ os ++ "/" ++ compilerName ++ "-"
        ++ showVersion compilerVersion {- @@@ -} ++ ", using " ++ show nCores ++ " of "
        ++ show maxNCores ++ " cores\n"
    
    mapM_ (\ex -> runInUnboundThread $ ex nCores) [katsura8, cyclic7, jason210]
