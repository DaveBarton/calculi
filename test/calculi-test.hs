import Math.Algebra.General.TestAlgebra
import Math.Algebra.Commutative.Field.TestZModP32
import Math.Algebra.Commutative.TestUPoly
import Math.Algebra.Commutative.TestEPoly

import Control.Monad (unless)
import System.Exit (exitFailure)


main    :: IO ()
main    = do
    ok      <- checkAll
        [testAlgebra, testZModP32, testUPoly, testEPoly {- @@ , other modules -}]
    unless ok exitFailure
