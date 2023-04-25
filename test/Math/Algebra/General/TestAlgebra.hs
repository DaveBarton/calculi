{-# LANGUAGE DataKinds #-}

{- |  This module helps test the "Algebra" module and its clients.  -}

module Math.Algebra.General.TestAlgebra (
    PropertyIO, property, propertyOnce, Range,
    TestRel, diffWith, TestOps(..), ShowGen, testOps0, tCheckBool, genVis,
    sameFun1TR, sameFunAABTR,
    symmetricProp, commutativeProp, antiSymmetricProp, associativeProp, identityProp,
    homomPT, endomPT,
    equalityProps, cmpProps, totalOrderProps,
    monoidProps,  abelianGroupProps, ringProps, ringHomomProps, fieldProps,
    moduleProps, rModProps, modRProps, rAlgProps,
    zzExpGen, zzGen, zzTestOps,
    pairTestOps,
    listShowWith, listTestOps, listTestEq, allPT, isSortedBy, slTestOps,
    readsProp,
    checkGroup, checkAll,
    testAlgebra
) where

import Math.Algebra.General.Algebra hiding (assert)

import Hedgehog (Gen, Property, PropertyName, PropertyT, Range,
    (===), annotate, annotateShow, assert, checkParallel, cover, diff, discard, failure,
    forAllWith, property, withDiscards, withTests)
import qualified Hedgehog as Hh
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import GHC.Records

import Control.Monad (unless, when)
import Data.Foldable (toList)
import Data.String (fromString)
import qualified StrictList2 as SL
import Text.Show (showListWith)


data ShowWith a     = ShowWith { _swShow :: a -> String, val :: a }
-- ^ for dynamically creating an instance of 'Show'

instance Show (ShowWith a) where
    show (ShowWith aShow a)     = aShow a


type PropertyIO     = PropertyT IO
-- ^ A @(PropertyIO a)@ produces an @a@ during a test. A @(PropertyIO ())@ runs a (part of a)
-- test.

propertyOnce        :: PropertyIO () -> Property
-- ^ a property with no random nonconstant generators, so it's only run once
propertyOnce propIO     = withTests 1 $ property propIO

type TestRel a      = a -> a -> PropertyIO ()
-- ^ Test that a result is (probably) correct, possibly generating random value(s) to help test.

diffWith            :: (a -> String) -> (a -> a -> Bool) -> TestRel a
-- ^ @diffWith aShow rel a b@ checks @rel a b@, and shows a git-like diff if the test fails.
diffWith aShow rel a b      = diff (ShowWith aShow a) (rel `on` (.val)) (ShowWith aShow b)

data TestOps a      = TestOps {
    tSP         :: ShowPrec a,
    tCheck      :: [String] -> a -> PropertyIO (),
                    -- ^ @tCheck notes a@ checks @a@ for invariants beyond just type-correctness
    gen         :: Gen a,       -- ^ optional
    eq          :: EqRel a      -- ^ optional
}
type ShowGen        = TestOps   -- ^ doesn't use 'eq'
instance HasField "tShow"   (TestOps a) (a -> String)   where
    getField (TestOps { tSP })  = tSP 0
instance HasField "tEq"     (TestOps a) (TestRel a)     where
    getField tT@(TestOps { tCheck, eq }) x y    = do
        tCheck [] x
        tCheck [] y
        diffWith tT.tShow eq x y

testOps0            :: (Eq a, Show a) => Gen a -> TestOps a
-- ^ 'TestOps' using 'Show' and 'Eq', and no invariant checking
testOps0 gen        = TestOps tSP (\_ _ -> pure ()) gen (==)
  where
    tSP prec a  = showsPrec prec a ""

tCheckBool          :: [String] -> Bool -> PropertyIO ()
tCheckBool notes ok =
    unless ok $ do
        mapM_ annotate notes
        failure

genVis              :: ShowGen a -> PropertyIO a
{- ^ Generate a visible (showable) random value for a property test. The value will be shown if
    the test fails. -}
genVis aT           = do
    a       <- forAllWith aT.tShow aT.gen
    aT.tCheck [] a
    pure a


sameFun1TR          :: ShowGen a -> TestRel b -> TestRel (a -> b)
sameFun1TR sga bTestEq f g  = do
    a       <- genVis sga
    bTestEq (f a) (g a)

sameFunAABTR        :: ShowGen a -> TestRel b -> TestRel (a -> a -> b)
sameFunAABTR sga bTestEq f g    = do
    x      <- genVis sga
    y      <- genVis sga
    bTestEq (f x y) (g x y)

symmetricProp       :: ShowGen a -> TestRel b -> (a -> a -> b) -> (PropertyName, Property)
symmetricProp sga bTestEq f     = ("symmetric", property $ sameFunAABTR sga bTestEq f (flip f))

commutativeProp     :: TestOps a -> Op2 a -> (PropertyName, Property)
commutativeProp aT op   = ("commutative", snd (symmetricProp aT aT.tEq op))

antiSymmetricProp   :: ShowGen a -> TestRel b -> Op1 b ->
                            (a -> a -> b) -> (PropertyName, Property)
antiSymmetricProp sga bTestEq bOpp f    =
    ("antiSymmetric", property $ sameFunAABTR sga bTestEq (bOpp .* f) (flip f))

associativeProp     :: TestOps a -> Op2 a -> (PropertyName, Property)
associativeProp aT (*~)     = ("associative", associative)
  where
    rand            = genVis aT
    associative     = property $ do
        a       <- rand
        b       <- rand
        c       <- rand
        aT.tEq ((a *~ b) *~ c) (a *~ (b *~ c))

identityProp        :: TestOps a -> Op2 a -> a -> (PropertyName, Property)
identityProp aT (*~) e  = ("identity", identity)
  where
    identity        = property $ do
        a       <- genVis aT
        aT.tEq (a *~ e) a
        aT.tEq a (a *~ e)

homomPT             :: ShowGen a -> Op2 a -> TestRel b -> Op2 b -> (a -> b) -> PropertyIO ()
-- ^ tests a homomorphism
homomPT sga aOp bTestEq bOp f   = sameFunAABTR sga bTestEq (f .* aOp) (bOp `on` f)

endomPT             :: TestOps a -> Op2 a -> Op1 a -> PropertyIO ()
-- ^ tests an endomomorphism (homomorphism a -> a)
endomPT aT op       = homomPT aT op aT.tEq op

equalityProps       :: ShowGen a -> EqRel a -> [(PropertyName, Property)]
-- ^ @|a| > 1@
equalityProps sg eq = [("reflexive", reflexive), ("symmetric", symmetric)]
  where
    rand            = genVis sg
    reflexive       = property $ do
        a       <- rand
        assert (eq a a)
    symmetric       = property $ do
        a       <- rand
        b       <- rand
        cover 1 "distinct" (not (eq a b))       -- to catch eq always returning True
        eq a b === eq b a   -- skip this for e.g. tEq of functions?
    {- Usually equal elements are stored in a unique normal form, or else equality checking is
        either slow or impossible. Thus testing transitivity seems either pointless, slow,
        impossible, or sometimes we don't even require @eq@ to be computationally transitive. -}

cmpProps                :: ShowGen a -> Cmp a -> [(PropertyName, Property)]
-- ^ @|a| > 1@
cmpProps sg cmp         =
    [("reflexive", reflexive), ("antisymmetric", antisymmetric), ("transitive", transitive)]
  where
    ordOpp          :: Ordering -> Ordering
    ordOpp r        = toEnum (2 - fromEnum r)
    ordSign         :: Ordering -> Int
    ordSign r       = fromEnum r - 1
    rand            = genVis sg
    reflexive       = property $ do     -- abstractly implied by antisymmetric
        a       <- rand
        cmp a a === EQ
    antisymmetric   = property $ do
        a       <- rand
        b       <- rand
        cover 1 "distinct" (cmp a b /= EQ)      -- to catch cmp always returning EQ
        ordOpp (cmp a b) === cmp b a
    transitive      = property $ do
        a       <- rand
        b       <- rand
        c       <- rand
        let n x y       = ordSign (cmp x y)
        n a b + n b c + n c a === - n a b * n b c * n c a

totalOrderProps         :: ShowGen a -> EqRel a -> Cmp a -> [(PropertyName, Property)]
-- ^ @equal@ must agree with abstract equality.
totalOrderProps sg equal cmp    = cmpProps sg cmp ++ [("fine", fine)]
  where
    fine            = property $ sameFunAABTR sg (===) (cmpEq cmp) equal

monoidProps             :: forall g. TestOps g -> MonoidFlags -> Group g ->
                            [(PropertyName, Property)]
monoidProps gT requiredFlags (Group { .. })     =
    [("required MonoidFlags", flagsOk)] ++
        equalityProps gT eq ++
        [associativeProp gT op, identityProp gT op ident,
            ("isIdentity", isIdentity),  ("identityIsIdentity", identityIsIdentity)] ++
        [("inverse", inverse) | hasEIBit monFlags IsGroup] ++
        [commutativeProp gT op | hasEIBit monFlags Abelian]
  where
    flagsOk         = propertyOnce $ do
        diff monFlags hasEIBits requiredFlags
    isIdentity      = property $ do
        a       <- genVis gT
        isIdent a === (a `eq` ident)
    identityIsIdentity  = propertyOnce $ do
        annotate $ gT.tShow ident
        assert (isIdent ident)
    inverse         = property $ do
        a       <- genVis gT
        let b   = inv a
        annotate $ gT.tShow b
        gT.tEq (a `op` b) ident
        gT.tEq ident (a `op` b)

abelianGroupProps       :: TestOps g -> AbelianGroup g -> [(PropertyName, Property)]
abelianGroupProps gT    = monoidProps gT agFlags

bDivProps               :: (r -> String) -> TestOps m -> Module r m ->
                            [(PropertyName, Property)]
bDivProps rShow mT (Module { .. })  =
    [("bDiv True", divProp (bDiv True)), ("bDiv False", divProp (bDiv False))]
  where
    divProp quoRemF     = property $ do
        y       <- genVis mT
        m       <- genVis mT
        let (q, r)  = quoRemF y m
        annotateShow [rShow q, mT.tShow r]
        mT.tEq y (ag.plus (scale q m) r)

ringProps               :: forall r. TestOps r -> RingFlags -> Ring r ->
                            [(PropertyName, Property)]
ringProps rT reqRingFlags rR@(Ring { .. })  =
    abelianGroupProps rT ag ++
        [("required RingFlags", ringFlagsOk),
         ("left distributive", leftDistrib), ("right distributive", rightDistrib),
         associativeProp rT times, identityProp rT times one] ++
        ringHomomProps zzTestOps zzRing rT.tEq rR fromZ ++
        bDivProps rT.tShow rT (Module ag (flip times) bDiv) ++
        [("nonzero", nonzero) | hasEIBit rFlags NotZeroRing] ++
        [commutativeProp rT times | hasEIBit rFlags IsCommutativeRing] ++
        [("no zero divisors", noZeroDivs) | hasEIBit rFlags NoZeroDivisors] ++
        [("inverses", inverses) | hasEIBit rFlags IsInversesRing]
  where
    AbelianGroup { .. }     = ag
    ringFlagsOk     = propertyOnce $ do
        diff rFlags hasEIBits reqRingFlags
    rand            = genVis rT
    leftDistrib     = property $ do
        a       <- rand
        endomPT rT plus (a `times`)
    rightDistrib    = property $ do
        a       <- rand
        endomPT rT plus (`times` a)
    nonzero         = propertyOnce $ do
        annotate $ rT.tShow one
        assert (not (isZero one))
    noZeroDivs      = property $ do
        a       <- rand
        b       <- rand
        assert (isZero a || isZero b || not (isZero (a `times` b)))
    inverses        = withDiscards 1000 $ property $ do
        m       <- rand
        when (isZero m) discard
        y       <- rand
        assert (divides rR m y)

ringHomomProps          :: ShowGen a -> Ring a -> TestRel b -> Ring b ->
                                (a -> b) -> [(PropertyName, Property)]
ringHomomProps sga aR bTestEq bR f  =
    [("additive homomorphism", property $ homomPT sga aR.plus bTestEq bR.plus f),
     ("multiplicative homomorphism", property $ homomPT sga aR.times bTestEq bR.times f),
     ("one ↦ one", propertyOnce $ bTestEq (f aR.one) bR.one)]

fieldProps              :: TestOps r -> Field r -> [(PropertyName, Property)]
fieldProps rT           = ringProps rT fieldFlags

moduleProps             :: Bool -> ShowGen r -> Ring r -> TestOps m ->
                            Module r m -> [(PropertyName, Property)]
moduleProps isLeftMod rT rR mT mM@(Module { .. })   =
    abelianGroupProps mT ag ++
        [("endM", endM), ("distribM", distribM), ("identityM", identityM), ("assocM", assocM)]
        ++ bDivProps rT.tShow mT mM
  where
    endM            = property $ do
        r       <- genVis rT
        endomPT mT ag.plus (scale r)
    distribM        = property $ do
        m       <- genVis mT
        homomPT rT rR.plus mT.tEq ag.plus (`scale` m)
    identityM       = property $
        sameFun1TR mT mT.tEq (scale rR.one) id
    (*~)            = (if isLeftMod then id else flip) rR.times
    assocM          = property $ do
        a       <- genVis rT
        b       <- genVis rT
        sameFun1TR mT mT.tEq (scale (a *~ b)) (scale a . scale b)

rModProps               :: ShowGen r -> Ring r -> TestOps m ->
                            RMod r m -> [(PropertyName, Property)]
rModProps               = moduleProps True

modRProps               :: ShowGen r -> Ring r -> TestOps m ->
                            ModR r m -> [(PropertyName, Property)]
modRProps               = moduleProps False

rAlgProps               :: ShowGen r -> Ring r -> TestOps a -> RingFlags ->
                            RAlg r a -> [(PropertyName, Property)]
rAlgProps rT rR aT reqAFlags (RAlg { .. })  =
    ringProps aT reqAFlags aR ++ ringHomomProps rT rR aT.tEq aR fromR ++
        [("centerA", centerA), ("scaleA", scaleA)]
  where
    (*~)            = aR.times
    centerA         = property $ do
        r       <- genVis rT
        let ra  = fromR r
        a       <- genVis aT
        aT.tEq (ra *~ a) (a *~ ra)
    scaleA          = property $ do
        r       <- genVis rT
        let ra  = fromR r
        sameFun1TR aT aT.tEq (scale r) (ra *~)


zzShowPrec              :: ShowPrec Integer
-- ^ 'timesSPrec' is smart about parenthesizing numbers, including negative numbers.
zzShowPrec prec n       = parensIf (n < 0 && exptPrec < prec) (show n)

zzExpGen                :: Integer -> Gen Integer
-- ^ @zzExpGen lim@ is an exponential generator with origin 0; @lim@ must be >= 0
zzExpGen lim            = Gen.integral (Range.exponentialFrom 0 (- lim) lim)

zzGen                   :: Gen Integer
zzGen                   = zzExpGen (2 ^ (98 :: Int))

zzTestOps               :: TestOps Integer
zzTestOps               = (testOps0 zzGen) { tSP = zzShowPrec }


showToShows             :: (a -> String) -> a -> ShowS
showToShows aShow a     = (aShow a ++)


pairTestOps             :: TestOps a -> TestOps b -> TestOps (a, b)
pairTestOps aT bT       = TestOps (const tShow) tCheck gen (pairEq aT.eq bT.eq)
  where
    tShow p         = pairShows (showToShows aT.tShow) (showToShows bT.tShow) p ""
    tCheck notes p@(a, b)   = do
        aT.tCheck notes1 a
        bT.tCheck notes1 b
      where
        notes1  = tShow p : notes
    gen             = liftA2 ( , ) aT.gen bT.gen


listShowWith            :: (a -> String) -> [a] -> String
listShowWith aShow as   = showListWith (showToShows aShow) as ""

listTestOps                 :: Range Int -> TestOps a -> TestOps [a]
listTestOps lenRange aT     = TestOps (const tShow) tCheck gen (liftEq aT.eq)
  where
    tShow           = listShowWith aT.tShow
    tCheck notes as = mapM_ (aT.tCheck (tShow as : notes)) as
    gen             = Gen.list lenRange aT.gen

listTestEq              :: TestOps a -> TestRel [a]
listTestEq aT           = (listTestOps undefined aT).tEq

allPT                   :: (a -> String) -> Pred a -> [a] -> PropertyIO ()
allPT aShow p as        = do
    let qs          = map p as
    unless (and qs) $ do
        annotate $ listShowWith aShow as
        annotateShow qs
        failure

-- |  The 'isSortedBy' function returns 'True' iff the predicate returns true
-- for all adjacent pairs of elements in the list.
isSortedBy              :: (a -> a -> Bool) -> [a] -> Bool
-- from Data.List.Ordered
isSortedBy lte          = loop
  where
    loop []         = True
    loop [_]        = True
    loop (x:y:zs)   = (x `lte` y) && loop (y:zs)


slTestOps               :: Range Int -> TestOps a -> TestOps (SL.List a)
slTestOps lenRange aT   = TestOps (const tShow) tCheck gen (SL.eqBy aT.eq)
  where
    tShow           = listShowWith aT.tShow . toList
    tCheck notes as = mapM_ (aT.tCheck (tShow as : notes)) as
    gen             = SL.fromList <$> Gen.list lenRange aT.gen


readsProp               :: TestOps a -> ReadS a -> (PropertyName, Property)
readsProp aT aReads     = ("read", readShow)
  where
    readShow        = property $ do
        a       <- genVis aT
        let xSs = aReads (aT.tShow a)
            xs  = [x | (x, "") <- xSs]
        annotateShow $ map snd xSs  -- tail string(s) after possible parses
        length xs === 1
        aT.tEq (head xs) a


checkGroup              :: String -> [(PropertyName, Property)] -> IO Bool
checkGroup name props   = checkParallel $ Hh.Group (fromString name) props

checkAll                :: [IO Bool] -> IO Bool
-- ^ like 'Control.Monad.Extra.andM', but doesn't short-circuit (it always runs all the tests),
-- and it prints the results.
checkAll checks         = do    -- liftM and (sequence checks)
    oks         <- sequence checks
    print oks
    pure (and oks)


testAlgebra             :: IO Bool
testAlgebra             =
    checkAll [
        checkGroup "zzRing" $ ringProps zzTestOps integralDomainFlags zzRing,
        checkGroup "Integer order, show/read" $
            totalOrderProps zzTestOps (==) compare ++ [readsProp zzTestOps reads]
        -- @@ , test more:
    ]
