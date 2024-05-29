import Test.Tasty (defaultMain)

import Math.Algebra.General.TestAlgebra
import Math.Algebra.Commutative.Field.TestZModPW
import Math.Algebra.Commutative.TestUPoly
import Math.Algebra.Commutative.TestEPoly
import Math.Algebra.Commutative.TestBinPoly


main    :: IO ()
main    = defaultMain $ testGroup "calculi"
    [algebraTests, zModPWTests, uPolyTests, ePolyTests, binPolyTests -- @@@ , sparseVectorTests
        {- @@ , other modules -}]
