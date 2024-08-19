{-# LANGUAGE DataKinds #-}

{- |  This module helps test the "Math.Algebra.General.Algebra" module and its clients.

    We use the [tasty](https://hackage.haskell.org/package/tasty) test framework to run
    [hedgehog](https://hackage.haskell.org/package/hedgehog) tests. These are \"property\"
    tests, where we generate pseudo-random values and test that functions on them have the
    desired properties, i.e. produce correct results. If a test fails, the pseudo-random values
    are \"shrunk\" in an effort to find a minimal failing test case, greatly easing debugging.
    :)
    
    Values are generated using the modules "Hedgehog.Gen" and "Hedgehog.Range", which are
    designed to be imported qualified. A 'Hedgehog.Gen' uses a 'Hedgehog.Size' to generate a
    pseudo-random value. A numeric value will be in a 'Hedgehog.Range.Range', and will shrink
    towards its \"origin\". For example:
    
    > import Math.Algebra.General.Algebra hiding (assert)
    > import Math.Algebra.General.TestAlgebra
    > import qualified Hedgehog.Gen as Gen
    > import qualified Hedgehog.Range as Range
    > import Test.Tasty (defaultMain)
    >
    > triangularNumber      :: Int -> Int
    > triangularNumber n    = n * (n + 1) `quot` 2
    >
    > triangularTM          :: TestM ()
    > triangularTM          = do
    >   let intTestOps  = testOps0 (Gen.int (Range.linear 1 100))
    >   n               <- genVis intTestOps
    >   triangularNumber n === sum [1 .. n]
    >
    > main = defaultMain $ testGroup "Tests" [
    >   singleTest "triangularNumber" triangularTM,
    >   ringTests zzTestOps (IsNontrivial True) integralDomainFlags zzRing
    >   ]
-}

module Math.Algebra.General.TestAlgebra (
    -- * Tasty imports
    -- | == From "Test.Tasty"
    TestName, TestTree, testGroup,
    
    -- * Hedgehog tests
    TestM, singleTest, testWith, testOnce, Range, TestRel, diffWith, (===),
    TestOps(TestOps, tSP, tCheck, gen, eq, ShowGen), ShowGen,
    annotateB, tAnnotate, tImageEq, testOps0, tCheckBool, genVis,
    
    -- * Function tests
    almostInjectiveTM, sameFun1TR, sameTMF1TR, sameFunAABTR, sameTMFAABTR,
    symmetricTest, commutativeTest, antiSymmetricTest, associativeTest, identityTest,
    homomTM, endomTM,
    
    -- * Algebra tests
    equalityTests, cmpTests, totalOrderTests,
    monoidTests,  abelianGroupTests, ringTests, ringHomomTests, fieldTests,
    moduleTests, rModTests, modRTests, rAlgTests,
    
    -- * Integer
    zzExpGen, zzGen, zzTestOps,
    
    -- * Pair
    pairTestOps,
    
    -- * List
    listTestOps, listTestEq, allTM, slTestOps,
    
    -- * Parse
    parseTest,
    
    -- * Variable names
    numVarTestOps,
    
    -- * Algebra module
    algebraTests
) where

import Math.Algebra.General.Algebra hiding (assert)

-- import Debug.Trace.Text (traceEvent)
import Hedgehog (Gen, Property, PropertyT, Range,
    (===), annotate, assert, cover, diff, discard, failure, forAllWith, property,
    withDiscards, withTests)
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)

import GHC.Records

import Control.Monad (join, unless, when)
-- import Control.Monad.IO.Class (liftIO)
import Data.Functor.Classes (liftEq, liftEq2)
import Data.Maybe (fromMaybe)
import Data.Strict.Tuple ((:!:), pattern (:!:))
import qualified Data.Text as T
import Fmt (Buildable, (+||), (||+), build, fmt, listF)
import qualified StrictList2 as SL


data ShowWith a     = ShowWith { _showT :: a -> Text, val :: a }
-- ^ for dynamically creating an instance of 'Show'

instance Show (ShowWith a) where
    show (ShowWith aShowT a)    = T.unpack (aShowT a)


-- * Hedgehog tests

type TestM          = PropertyT IO
{- ^ 'TestM' is a 'Monad' for testing. A @(TestM v)@ produces a @(v)@ during a test. A
    @(TestM ())@ runs a (part of a) test. Neither contains any test configuration (number of
    test runs, max shrinks, etc.).
    
    A 'TestM' is a 'Hedgehog.MonadTest' (and a 'Hedgehog.MonadIO', etc.) so during a test you
    can use it to call functions in "Hedgehog" like 'annotate', 'assert', '(===)', 'failure',
    'cover', 'Hedgehog.discard', etc.
    
    If the test fails, "Hedgehog" will try to shrink the failing test case, and then print it
    and other information for debugging. -}

singleTest          :: TestName -> TestM () -> TestTree
-- ^ Create a named test with the default configuration.
singleTest name     = testProperty name . property

testWith            :: TestName -> Op1 Property -> TestM () -> TestTree
{- ^ Create a named test with a custom configuration. Use "Hedgehog" functions like 'withTests',
    'withDiscards', etc. to create an @(Op1 Property)@ to modify the default configuration. -}
testWith name mods  = testProperty name . mods . property

testOnce            :: TestName -> TestM () -> TestTree
-- ^ Create a named test that has no random nonconstant generators, so it's only run once.
testOnce name       = testWith name (withTests 1)

type TestRel a      = a -> a -> TestM ()
{- ^ A @(TestRel a)@ tests that a relation (probably) holds, possibly generating random value(s)
    to help test. Usually the relation is equality, unless otherwise noted. On failure, the
    @TestRel@ shows where the values differ or the relation fails to hold. Often the @TestRel@
    also calls 'tCheck', as its documentation may state. -}

diffWith            :: (a -> Text) -> (a -> a -> Bool) -> TestRel a
{- ^ @(diffWith aShowT rel x y)@ checks @(rel x y)@, and shows a git-like diff if the test
    fails. -}
diffWith aShowT rel a b     = diff (ShowWith aShowT a) (rel `on` (.val)) (ShowWith aShowT b)

{- | A @(TestOps a)@ contains operations to help test the type @(a)@. -}
data TestOps a      = TestOps {
    tSP         :: ShowPrec a,
    tCheck      :: [Text] -> a -> TestM (),
        {- ^ @(tCheck notes x)@ checks @x@ for invariants beyond just type-correctness. On
            failure, it shows the problem, @x@, and these additional @notes@ of context. -}
    gen         :: Gen a,       -- ^ optional; generates a pseudo-random @(a)@
    eq          :: EqRel a      -- ^ optional; an equality function for checking test results
}

type ShowGen        = TestOps
{- ^ A @(ShowGen a)@ is for showing and generating values of type @(a)@; its 'TestAlgebra.eq' is
    not used. -}

pattern ShowGen     :: ShowPrec a -> ([Text] -> a -> TestM ()) -> Gen a -> ShowGen a
-- ^ v'TestOps' but ignoring 'TestAlgebra.eq'
pattern
    ShowGen tSP tCheck gen  <- TestOps tSP tCheck gen _     where
    ShowGen tSP tCheck gen  =  TestOps tSP tCheck gen (\_ _ -> error "ShowGen: eq is illegal")
{-# COMPLETE ShowGen #-}

instance HasField "tShowT"  (TestOps a) (a -> Text)   where
    getField (TestOps { tSP })  = (.t) . tSP

instance HasField "tEq"     (TestOps a) (TestRel a)     where
    getField tTA@(TestOps { tCheck, eq }) x y   = do
        tCheck [] x
        tCheck [] y
        diffWith tTA.tShowT eq x y
-- ^ tests that a result satisfies the invariants for an @(a)@, and equals an expected value

annotateB           :: Buildable b => b -> TestM ()
-- ^ Annotate with textual information that will be shown if the current test fails.
annotateB           = annotate . fmt . build

tAnnotate           :: TestOps a -> a -> TestM a
-- ^ 'tCheck' an intermediate result, return it, and show it if the test fails.
tAnnotate aTA a     = do
    aTA.tCheck [] a
    annotate (T.unpack (aTA.tShowT a))
    pure a

tImageEq            :: TestOps a -> TestRel b -> (a -> b) -> a -> b -> TestM ()
-- ^ 'tAnnotate' an intermediate result of type @(a)@, and test its image under a map.
tImageEq aTA bTestEq f a b  = do
    b'          <- f <$> tAnnotate aTA a
    bTestEq b' b

testOps0            :: (Eq a, Show a) => Gen a -> TestOps a
-- ^ v'TestOps' using 'show' (not 'showsPrec'), 'AtomPrec', and 'Eq', and no invariant checking.
testOps0 gen        = TestOps tSP (\_ _ -> pure ()) gen (==)
  where
    tSP a       = PrecText AtomPrec (showT a)

tCheckBool          :: [Text] -> Bool -> TestM ()
-- ^ Check the 'Bool' is 'True', showing the notes on failure.
tCheckBool notes ok =
    unless ok $ do
        mapM_ annotateB notes
        failure

genVis              :: ShowGen a -> TestM a
{- ^ Generate a visible (showable) random value for a property test, and 'tCheck' it. The value
    will be shown if the test fails, to help with debugging. -}
genVis aTA          = do
    a       <- forAllWith (T.unpack . aTA.tShowT) aTA.gen
    aTA.tCheck [] a
    pure a


-- * Function tests

almostInjectiveTM   :: TestOps a -> EqRel b -> (a -> b) -> TestM ()
{- ^ Test that a function @f@ almost always takes distinct (unequal) elements to distinct
    elements. Then one can test values of type @(a)@ using @(tImageEq aTA bTestEq f)@. -}
almostInjectiveTM aTA bEq f     = do
    x       <- genVis aTA
    y       <- genVis aTA
    cover 90 "injective" (aTA.eq x y || not (bEq (f x) (f y)))

sameFun1TR          :: ShowGen a -> TestRel b -> TestRel (a -> b)
-- ^ test two functions are equal
sameFun1TR sga bTestEq f g  = do
    a       <- genVis sga
    bTestEq (f a) (g a)

sameTMF1TR          :: ShowGen a -> TestRel b -> TestRel (a -> TestM b)
-- ^ test two functions are equal
sameTMF1TR sga bTestEq f g  = do
    a       <- genVis sga
    join $ liftA2 bTestEq (f a) (g a)

sameFunAABTR        :: ShowGen a -> TestRel b -> TestRel (a -> a -> b)
-- ^ test two functions of type @(a -> a -> b)@ are equal
sameFunAABTR sga bTestEq f g    = do
    x      <- genVis sga
    y      <- genVis sga
    bTestEq (f x y) (g x y)

sameTMFAABTR        :: ShowGen a -> TestRel b -> TestRel (a -> a -> TestM b)
-- ^ test two functions of type @(a -> a -> TestM b)@ are equal
sameTMFAABTR sga bTestEq f g    = do
    x      <- genVis sga
    y      <- genVis sga
    join $ liftA2 bTestEq (f x y) (g x y)

symmetricTest       :: Maybe TestName -> ShowGen a -> TestRel b -> (a -> a -> b) -> TestTree
-- ^ test a function is symmetric (@f x y = f y x@)
symmetricTest name sga bTestEq f    =
    singleTest (fromMaybe "symmetric" name) $ sameFunAABTR sga bTestEq f (flip f)

commutativeTest     :: TestOps a -> Op2 a -> TestTree
{- ^ Test a function of type @(a -> a -> a)@ is commutative (@f x y = f y x@), and 'tCheck' its
    results. -}
commutativeTest aTA = symmetricTest (Just "commutative") aTA aTA.tEq

antiSymmetricTest   :: ShowGen a -> TestRel b -> Op1 b ->
                            (a -> a -> b) -> TestTree
-- ^ test a function is antisymmetric (@f x y = - f y x@, where @(-)@ is the @(Op1 b)@)
antiSymmetricTest sga bTestEq bOpp f    =
    singleTest "antiSymmetric" $ sameFunAABTR sga bTestEq (bOpp .* f) (flip f)

associativeTest     :: TestOps a -> Op2 a -> TestTree
{- ^ Test a function is associative @((x \`op\` y) \`op\` z = x \`op\` (y \`op\` z))@, and
    'tCheck' its results. -}
associativeTest aTA (*~)    = associative
  where
    rand            = genVis aTA
    associative     = singleTest "associative" $ do
        a       <- rand
        b       <- rand
        c       <- rand
        ab      <- tAnnotate aTA (a *~ b)
        bc      <- tAnnotate aTA (b *~ c)
        aTA.tEq (ab *~ c) (a *~ bc)

identityTest        :: TestOps a -> Op2 a -> a -> TestTree
{- ^ Test an element is the identity for an @(Op2 a)@:
    @x \`op\` e = e \`op\` x = x@ for all @x@; and 'tCheck' the element. -}
identityTest aTA (*~) e     = testGroup "identity element" [identityOk, identity]
  where
    identityOk      = testOnce "identityOk" $ aTA.tCheck [] e
    identity        = singleTest "identity" $ do
        a       <- genVis aTA
        aTA.tEq (a *~ e) a
        aTA.tEq a (a *~ e)

homomTM             :: ShowGen a -> Op2 a -> TestRel b -> Op2 b -> (a -> b) -> TestM ()
-- ^ test a function is a homomorphism @(f (x \`aOp\` y) = f x \`bOp\` f y)@
homomTM sga aOp bTestEq bOp f   = sameFunAABTR sga bTestEq (f .* aOp) (bOp `on` f)

endomTM             :: TestOps a -> Op2 a -> Op1 a -> TestM ()
-- ^ test a function is an endomorphism (homomorphism from @(a)@ to @(a)@)
endomTM aTA op      = homomTM aTA op aTA.tEq op


-- * Algebra tests

equalityTests       :: ShowGen a -> IsNontrivial -> EqRel a -> TestTree
{- ^ Try to test a function is a good equality function. This checks (@eq@) is reflexive
    (@x \`eq\` x@), symmetric (@x \`eq\` y => y \`eq\` x@), and if nontrivial then doesn't
    always return @True@. -}
equalityTests sg nontriv eq     = testGroup "Equality" [reflexive, symmetric]
  where
    rand            = genVis sg
    reflexive       = singleTest "reflexive" $ do
        a       <- rand
        assert (eq a a)
    symmetric       = singleTest "symmetric" $ do
        a       <- rand
        b       <- rand
        when nontriv.b $ cover 1 "distinct" (not (eq a b))  -- to catch eq always returning True
        eq a b === eq b a   -- skip this for e.g. tEq of functions?
    {- Usually equal elements are stored in a unique normal form, or else equality checking is
        either slow or impossible. Thus testing transitivity seems either pointless, slow,
        impossible, or sometimes we don't even require @eq@ to be computationally transitive. -}

cmpTests                :: ShowGen a -> IsNontrivial -> Cmp a -> TestTree
{- ^ Test that a @('Cmp' a)@ has its required properties (antisymmetric and transitive), and if
    nontrivial then it doesn't always return 'EQ'. -}
cmpTests sg nontriv cmp     = testGroup "Comparison" [reflexive, antisymmetric, transitive]
  where
    ordOpp          :: Ordering -> Ordering
    ordOpp r        = toEnum (2 - fromEnum r)
    ordSign         :: Ordering -> Int
    ordSign r       = fromEnum r - 1
    rand            = genVis sg
    reflexive       = singleTest "reflexive" $ do   -- abstractly implied by antisymmetric
        a       <- rand
        cmp a a === EQ
    antisymmetric   = singleTest "antisymmetric" $ do
        a       <- rand
        b       <- rand
        when nontriv.b $ cover 1 "distinct" (cmp a b /= EQ) -- to catch cmp always returning EQ
        ordOpp (cmp a b) === cmp b a
    transitive      = singleTest "transitive" $ do
        a       <- rand
        b       <- rand
        c       <- rand
        let n x y       = ordSign (cmp x y)
        n a b + n b c + n c a === - n a b * n b c * n c a

totalOrderTests         :: ShowGen a -> EqRel a -> IsNontrivial -> Cmp a -> TestTree
{- ^ Test that a @('Cmp' a)@ is a total order. The @(EqRel a)@ argument must agree with abstract
    equality. -}
totalOrderTests sg equal nontriv cmp    =
    testGroup "Total Order" [cmpTests sg nontriv cmp, fine]
  where
    fine            = singleTest "fine" $ sameFunAABTR sg (===) (cmpEq cmp) equal

monoidTests             :: TestOps g -> MonoidFlags -> MonoidOps g -> TestTree
{- ^ Test the algebra is a Monoid including the given t'MonoidFlags'. If 'Algebra.eq' and
    'Algebra.op' are correct, then this tests whether all the Monoid or 'Group' operations are
    correct, and 'tCheck's their results. -}
monoidTests gTA requiredFlags (MkMonoid { .. })     = testGroup "Monoid" $
    [flagsOk, equalityTests gTA (IsNontrivial monFlags.nontrivial) eq,
        associativeTest gTA op, identityTest gTA op ident, isIdentity, identityIsIdentity] ++
    [inverse                | monFlags.isGroup] ++
    [commutativeTest gTA op | monFlags.abelian]
  where
    flagsOk         = testOnce "required MonoidFlags" $
        diff monFlags flagsContain requiredFlags
    isIdentity      = singleTest "isIdentity" $ do
        a       <- genVis gTA
        isIdent a === (a `eq` ident)
    identityIsIdentity  = testOnce "identityIsIdentity" $
        assert . isIdent =<< tAnnotate gTA ident
    inverse         = singleTest "inverse" $ do
        a       <- genVis gTA
        b       <- tAnnotate gTA $ inv a
        gTA.tEq (a `op` b) ident
        gTA.tEq ident (a `op` b)

abelianGroupTests       :: TestOps g -> IsNontrivial -> AbelianGroup g -> TestTree
{- ^ Test the algebra is an t'AbelianGroup'. If 'Algebra.eq' and 'Algebra.plus' are correct,
    then this tests whether all the t'AbelianGroup' operations are correct, and 'tCheck's their
    results. -}
abelianGroupTests gTA nontriv   = monoidTests gTA (agFlags nontriv)

bDivTests               :: TestOps q -> TestOps m -> Module q m -> TestTree
{- ^ Test @(y = m*q + r)@, and 'tCheck' @q@ and @r@. The attempted minimalness of @(r)@ is not
    tested. -}
bDivTests qTA mTA (Module { .. })   = testGroup "bDiv"
    [divTest doFull | doFull <- IsDeep <$> [False, True]]
  where
    divTest doFull      = singleTest ("bDiv ("+||doFull||+")") $ do
        y       <- genVis mTA
        m       <- genVis mTA
        let (q, r)  = bDiv doFull y m
        _       <- tAnnotate qTA q
        _       <- tAnnotate mTA r
        mTA.tEq y (ag.plus (scale q m) r)

ringTests               :: TestOps r -> IsNontrivial -> RingFlags -> Ring r -> TestTree
{- ^ Test the algebra is a t'Ring' including the given flags. If 'Algebra.eq', 'Algebra.plus',
    and 'Algebra.times' are correct, then this tests whether all the t'Ring' operations are
    correct, except for the minimalness of remainders. This also 'tCheck's the results of all
    the t'Ring' operations. -}
ringTests rTA nontriv reqRingFlags rR@(Ring { .. })     = testGroup "Ring" $
    [abelianGroupTests rTA nontriv ag, ringFlagsOk, leftDistrib, rightDistrib,
        associativeTest rTA times, identityTest rTA times one,
        ringHomomTests (Just "Ring Homomorphism from Z") zzTestOps zzRing rTA.tEq rR fromZ,
        bDivTests rTA rTA (Module ag (flip times) bDiv)] ++
    [commutativeTest rTA times  | rFlags.commutative] ++
    [noZeroDivs                 | rFlags.noZeroDivisors] ++
    [inverses                   | rFlags.nzInverses]
  where
    AbelianGroup { .. }     = ag
    ringFlagsOk     = testOnce "required RingFlags" $ do
        diff rFlags flagsContain reqRingFlags
    rand            = genVis rTA
    leftDistrib     = singleTest "left distributive" $ do
        a       <- rand
        endomTM rTA plus (a `times`)
    rightDistrib    = singleTest "right distributive" $ do
        a       <- rand
        endomTM rTA plus (`times` a)
    noZeroDivs      = singleTest "no zero divisors" $ do
        a       <- rand
        b       <- rand
        assert (isZero a || isZero b || not (isZero (a `times` b)))
    inverses        = testWith "inverses" (withDiscards 1000) $ do
        m       <- rand
        when (isZero m) discard
        y       <- rand
        assert (divides rR m y)

ringHomomTests          :: Maybe TestName -> ShowGen a -> Ring a -> TestRel b -> Ring b ->
                                (a -> b) -> TestTree
{- ^ Test a function is a ring homomorphism, assuming the rings are correct. Then this test also
    implies @f(0) = 0@, @f(- x) = - f(x)@, @f@ is well-defined, and @f . aR.fromZ = bR.fromZ@.
    -}
ringHomomTests mName sga aR bTestEq bR f     = testGroup (fromMaybe "Ring Homomorphism" mName)
    [singleTest "additive homomorphism" $ homomTM sga aR.plus bTestEq bR.plus f,
     singleTest "multiplicative homomorphism" $ homomTM sga aR.times bTestEq bR.times f,
     testOnce "one ↦ one" $ bTestEq (f aR.one) bR.one]

fieldTests              :: TestOps r -> Field r -> TestTree
{- ^ Test the algebra is a t'Field'. If 'Algebra.eq', 'Algebra.plus', and 'Algebra.times' are
    correct, then this tests whether all the t'Field' operations are correct and 'tCheck's their
    results. -}
fieldTests rTA          = ringTests rTA (IsNontrivial True) fieldFlags

moduleTests             :: IsLeftMod -> ShowGen r -> Ring r -> TestOps m ->
                            IsNontrivial -> Module r m -> TestTree
{- ^ Test that @(m)@ is a t'Module' over @(r)@, assuming that @(r)@'s ring operations are
    correct. This also 'tCheck's the results of the t'Module' operations. -}
moduleTests isLeftMod rTA rR mTA nontriv mM@(Module { .. })     =
    testGroup ((if isLeftMod.b then "Left" else "Right") <> " Module")
        [abelianGroupTests mTA nontriv ag, scaleOk, endoM, distribM, identityM, assocM,
            bDivTests rTA mTA mM]
  where
    scaleOk         = singleTest "scaleOk" $ do
        r       <- genVis rTA
        m       <- genVis mTA
        mTA.tCheck [] (scale r m)
    endoM           = singleTest "endoM" $ do
        r       <- genVis rTA
        endomTM mTA ag.plus (scale r)
    distribM        = singleTest "distribM" $ do
        m       <- genVis mTA
        homomTM rTA rR.plus mTA.tEq ag.plus (`scale` m)
    identityM       = singleTest "identityM" $
        sameFun1TR mTA mTA.tEq (scale rR.one) id
    (*~)            = (if isLeftMod.b then id else flip) rR.times
    assocM          = singleTest "assocM" $ do
        a       <- genVis rTA
        b       <- genVis rTA
        sameFun1TR mTA mTA.tEq (scale (a *~ b)) (scale a . scale b)

rModTests               :: ShowGen r -> Ring r -> TestOps m ->
                            IsNontrivial -> RMod r m -> TestTree
-- ^ > rModTests = moduleTests (IsLeftMod True)
rModTests               = moduleTests (IsLeftMod True)

modRTests               :: ShowGen r -> Ring r -> TestOps m ->
                            IsNontrivial -> ModR r m -> TestTree
-- ^ > modRTests = moduleTests (IsLeftMod False)
modRTests               = moduleTests (IsLeftMod False)

rAlgTests               :: ShowGen r -> Ring r -> TestOps a ->
                            IsNontrivial -> RingFlags -> RAlg r a -> TestTree
{- ^ Test that @(a)@ is an t'RAlg' over @(r)@, including the given flags, assuming that the
    @(Ring r)@ is correct. This also 'tCheck's the results of the t'RAlg' operations. -}
rAlgTests rTA rR aTA nontriv reqAFlags (RAlg { .. })    = testGroup "R-Algebra"
    [ringTests aTA nontriv reqAFlags aR, ringHomomTests Nothing rTA rR aTA.tEq aR fromR,
        centerA, scaleA]
  where
    (*~)            = aR.times
    centerA         = singleTest "centerA" $ do
        r       <- genVis rTA
        let ra  = fromR r
        aTA.tCheck [] ra
        a       <- genVis aTA
        aTA.tEq (ra *~ a) (a *~ ra)
    scaleA          = singleTest "scaleA" $ do
        r       <- genVis rTA
        let ra  = fromR r
        sameFun1TR aTA aTA.tEq (scale r) (ra *~)


-- * Integer

zzExpGen                :: Integer -> Gen Integer
{- ^ @(zzExpGen lim)@ is an \"exponential\" (see 'Hedgehog.Range.exponentialFrom') generator
    from @(- lim)@ to @(lim)@ with origin 0; @lim@ must be >= 0. -}
zzExpGen lim            = Gen.integral (Range.exponentialFrom 0 (- lim) lim)

zzGen                   :: Gen Integer
-- ^ a common exponential generator, producing 'Integer's that do and don't fit in an 'Int'
zzGen                   = zzExpGen (2 ^ (98 :: Int))

zzTestOps               :: TestOps Integer
-- ^ t'TestOps' using 'zzGen'
zzTestOps               = (testOps0 zzGen) { tSP = zzShowPrec }


-- * Pair

pairTestOps             :: TestOps a -> TestOps b -> TestOps (a :!: b)
-- ^ t'TestOps' for a pair
pairTestOps aTA bTA     = TestOps tSP tCheck gen (liftEq2 aTA.eq bTA.eq)
  where
    tSP             = sPairShowPrec aTA.tSP bTA.tSP
    tCheck notes p@(a :!: b)    = do
        aTA.tCheck notes1 a
        bTA.tCheck notes1 b
      where
        notes1  = (tSP p).t : notes
    gen             = liftA2 (:!:) aTA.gen bTA.gen


-- * List

listTestOps                 :: Range Int -> TestOps a -> TestOps [a]
-- ^ t'TestOps' for a list, given a 'Hedgehog.Range.Range' for the length
listTestOps lenRange aTA    = TestOps tSP tCheck gen (liftEq aTA.eq)
  where
    tSP             = listShowPrec aTA.tSP
    tCheck notes as = mapM_ (aTA.tCheck ((tSP as).t : notes)) as
    gen             = Gen.list lenRange aTA.gen

listTestEq              :: TestOps a -> TestRel [a]
-- ^ test two lists are equal
listTestEq aTA          = (listTestOps undefined aTA).tEq

allTM                   :: (Functor f, Foldable f) => ShowPrec a -> Pred a -> f a -> TestM ()
-- ^ test all elements of a list (or list-like) satisfy a predicate
allTM aSP p as          = do
    let qs          = fmap p as
    unless (and qs) $ do
        annotateB $ listShowPrec aSP as
        annotateB $ listF qs
        failure


slTestOps               :: Range Int -> TestOps a -> TestOps (SL.List a)
-- ^ t'TestOps' for a strict list, given a 'Hedgehog.Range.Range' for the length
slTestOps lenRange aTA  = TestOps tSP tCheck gen (SL.eqBy aTA.eq)
  where
    tSP             = listShowPrec aTA.tSP
    tCheck notes as = mapM_ (aTA.tCheck ((tSP as).t : notes)) as
    gen             = SL.fromList <$> Gen.list lenRange aTA.gen


-- * Parse

parseTest               :: TestOps a -> Parser a -> TestTree
-- ^ Test that reading a shown value produces the original value, and 'tCheck' the read value.
parseTest aTA aParse    = readShow
  where
    readShow        = singleTest "parse" $ do
        a       <- genVis aTA
        let b   = parseAllOrErr aParse (aTA.tShowT a)   -- don't use 'error'?
        aTA.tEq a b


-- * Variable names

numVarTestOps   :: Text -> Gen Int -> TestOps Int
-- Create test operations for numbered variables, given a prefix.
numVarTestOps prefix gen    = (testOps0 gen) { tSP = numVarPT prefix }


-- * Algebra module

algebraTests            :: TestTree
-- ^ Test the "Math.Algebra.General.Algebra" module.
algebraTests            =
    testGroup "Algebra.hs" [
        testGroup "Integer"
            [ringTests zzTestOps (IsNontrivial True) integralDomainFlags zzRing,
                totalOrderTests zzTestOps (==) (IsNontrivial True) compare,
                parseTest zzTestOps zzParse]
        -- @@ , test more:
    ]
