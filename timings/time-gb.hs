{-# LANGUAGE CPP #-}

import Math.Algebra.Commutative.GBDemo

import Control.Concurrent (getNumCapabilities, runInUnboundThread)
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
import Control.Monad (void)
import System.Process (callCommand)


main    :: IO ()
main    = do
    void $ try @SomeException $ callCommand "sysctl vm.loadavg"
    void $ try @SomeException $ callCommand "sysctl hw.physicalcpu"
    
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
    
    mapM_ (\ex -> runInUnboundThread $ ex nCores) [katsura8, cyclic7, jason210]
