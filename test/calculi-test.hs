import Math.Algebra.General.TestAlgebra
import Math.Algebra.Commutative.Field.TestZModP32
import Math.Algebra.Commutative.TestUPoly
import Math.Algebra.Commutative.TestEPoly
import Math.Algebra.Commutative.TestBinPoly

import System.Exit (exitSuccess, exitFailure)


main    :: IO ()
main    = do
    ok      <- checkAll
        [testAlgebra, testZModP32, testUPoly, testEPoly, testBinPoly {- @@ , other modules -}]
    if ok then exitSuccess else exitFailure
