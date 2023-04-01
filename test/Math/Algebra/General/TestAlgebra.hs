{- |  This module helps test the "Algebra" module and its clients.  -}

module Math.Algebra.General.TestAlgebra (
    ShowGen, PropertyIO, genVis, TestRel, diffWith, TestOps, property, propertyOnce,
    sameFun1PT, sameFunAABPT,
    symmetricProp, commutativeProp, antiSymmetricProp, associativeProp, identityProp,
    homomPT, endomPT,
    equalityProps, cmpProps, totalOrderProps,
    monoidProps,  abelianGroupProps, ringProps, ringHomomProps, fieldProps,
    moduleProps, rModProps, modRProps, rAlgProps,
    zzExpGen, zzGen, zzShowGen, zzTestOps,
    pairTestOps, listShowWith, listShowGen, listTestEq, listTestOps,
    readsProp,
    checkGroup, checkAll,
    testAlgebra
) where

import Math.Algebra.General.Algebra hiding (assert)

import Hedgehog (Gen, Property, PropertyName, PropertyT, Range,
    (===), annotate, annotateShow, assert, checkParallel, cover, diff, discard, forAllWith,
    property, withDiscards, withTests)
import qualified Hedgehog as Hh
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Monad (liftM2, when, zipWithM_)
import Data.String (fromString)
import Text.Show (showListWith)


data ShowWith a     = ShowWith { _swShow :: a -> String, val :: a }
-- ^ for dynamically creating an instance of 'Show'

instance Show (ShowWith a) where
    show (ShowWith aShow a)     = aShow a


type ShowGen a      = (a -> String, Gen a)

type PropertyIO     = PropertyT IO
-- ^ A @(PropertyIO a)@ produces an @a@ during a test. A @(PropertyIO ())@ runs a (part of a)
-- ^ test.

genVis              :: ShowGen a -> PropertyIO a
{- ^ Generate a visible (showable) random value for a property test. The value will be shown if
    the test fails. -}
genVis              = uncurry forAllWith

type TestRel a      = a -> a -> PropertyIO ()
-- ^ Test that a result is (probably) correct, possibly generating random value(s) to help test.

diffWith            :: (a -> String) -> (a -> a -> Bool) -> TestRel a
-- ^ @diffWith aShow rel a b@ checks @rel a b@, and shows a git-like diff if the test fails.
diffWith aShow rel a b      = diff (ShowWith aShow a) (rel `on` (.val)) (ShowWith aShow b)

type TestOps a      = (ShowGen a, TestRel a)

propertyOnce        :: PropertyIO () -> Property
-- ^ a property with no random nonconstant generators, so it's only run once
propertyOnce propIO     = withTests 1 $ property propIO


sameFun1PT          :: ShowGen a -> TestRel b -> TestRel (a -> b)
sameFun1PT sga bTestEq f g  = do
    a       <- genVis sga
    bTestEq (f a) (g a)

sameFunAABPT        :: ShowGen a -> TestRel b -> TestRel (a -> a -> b)
sameFunAABPT sga bTestEq f g    = do
    x      <- genVis sga
    y      <- genVis sga
    bTestEq (f x y) (g x y)

symmetricProp       :: ShowGen a -> TestRel b -> (a -> a -> b) -> (PropertyName, Property)
symmetricProp sga bTestEq f     = ("symmetric", property $ sameFunAABPT sga bTestEq f (flip f))

commutativeProp     :: ShowGen a -> TestRel a -> Op2 a -> (PropertyName, Property)
commutativeProp sg testEq op    = ("commutative", snd (symmetricProp sg testEq op))

antiSymmetricProp   :: ShowGen a -> TestRel b -> Op1 b ->
                            (a -> a -> b) -> (PropertyName, Property)
antiSymmetricProp sga bTestEq bOpp f    =
    ("antiSymmetric", property $ sameFunAABPT sga bTestEq (bOpp .* f) (flip f))

associativeProp     :: ShowGen a -> TestRel a -> Op2 a -> (PropertyName, Property)
associativeProp sg testEq (*~)  = ("associative", associative)
  where
    rand            = genVis sg
    associative     = property $ do
        a       <- rand
        b       <- rand
        c       <- rand
        testEq ((a *~ b) *~ c) (a *~ (b *~ c))

identityProp        :: ShowGen a -> TestRel a -> Op2 a -> a -> (PropertyName, Property)
identityProp sg testEq (*~) e   = ("identity", identity)
  where
    identity        = property $ do
        a       <- genVis sg
        testEq (a *~ e) a
        testEq a (a *~ e)

homomPT             :: ShowGen a -> Op2 a -> TestRel b -> Op2 b -> (a -> b) -> PropertyIO ()
-- ^ tests a homomorphism
homomPT sga aOp bTestEq bOp f   = sameFunAABPT sga bTestEq (f .* aOp) (bOp `on` f)

endomPT             :: ShowGen a -> TestRel a -> Op2 a -> Op1 a -> PropertyIO ()
-- ^ tests an endomomorphism (homomorphism a -> a)
endomPT sg testEq op    = homomPT sg op testEq op

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
        eq a b === eq b a   -- skip this for e.g. testEq of functions?
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
    fine            = property $ sameFunAABPT sg (===) (cmpEq cmp) equal

monoidProps             :: forall g. ShowGen g -> TestRel g -> MonoidFlags -> Group g ->
                            [(PropertyName, Property)]
monoidProps sg@(gShow, _) testEq requiredFlags (Group { .. })   =
    [("required MonoidFlags", flagsOk)] ++
        equalityProps sg eq ++
        [associativeProp sg testEq op, identityProp sg testEq op ident,
            ("isIdentity", isIdentity),  ("identityIsIdentity", identityIsIdentity)] ++
        [("inverse", inverse) | hasEIBit monFlags IsGroup] ++
        [commutativeProp sg testEq op | hasEIBit monFlags Abelian]
  where
    flagsOk         = propertyOnce $ do
        annotateShow [monFlags, requiredFlags]
        assert (hasEIBits monFlags requiredFlags)
    isIdentity      = property $ do
        a       <- genVis sg
        isIdent a === (a `eq` ident)
    identityIsIdentity  = propertyOnce $ do
        annotate $ gShow ident
        assert (isIdent ident)
    inverse         = property $ do
        a       <- genVis sg
        let b   = inv a
        annotate $ gShow b
        testEq (a `op` b) ident
        testEq ident (a `op` b)

abelianGroupProps       :: ShowGen g -> TestRel g -> AbelianGroup g ->
                                [(PropertyName, Property)]
abelianGroupProps sg testEq     = monoidProps sg testEq agFlags

bDivProps               :: (r -> String) -> ShowGen m -> TestRel m -> Module r m ->
                            [(PropertyName, Property)]
bDivProps rShow sgm@(mShow, _) mTestEq (Module { .. })  =
    [("bDiv True", divProp (bDiv True)), ("bDiv False", divProp (bDiv False))]
  where
    divProp quoRemF     = property $ do
        y       <- genVis sgm
        m       <- genVis sgm
        let (q, r)  = quoRemF y m
        annotateShow $ [rShow q, mShow r]
        mTestEq y (ag.plus (scale q m) r)

ringProps               :: forall r. ShowGen r -> TestRel r -> RingFlags -> Ring r ->
                            [(PropertyName, Property)]
ringProps sg@(rShow, _) testEq reqRingFlags rR@(Ring { .. })    =
    abelianGroupProps sg testEq ag ++
        [("required RingFlags", ringFlagsOk),
         ("left distributive", leftDistrib), ("right distributive", rightDistrib),
         associativeProp sg testEq times, identityProp sg testEq times one] ++
        ringHomomProps zzShowGen zzRing testEq rR fromZ ++
        bDivProps rShow sg testEq (Module ag (flip times) bDiv) ++
        [("nonzero", nonzero) | hasEIBit rFlags NotZeroRing] ++
        [commutativeProp sg testEq times | hasEIBit rFlags IsCommutativeRing] ++
        [("no zero divisors", noZeroDivs) | hasEIBit rFlags NoZeroDivisors] ++
        [("inverses", inverses) | hasEIBit rFlags IsInversesRing]
  where
    AbelianGroup { .. }     = ag
    ringFlagsOk     = propertyOnce $ do
        annotateShow [rFlags, reqRingFlags]
        assert (hasEIBits rFlags reqRingFlags)
    rand            = genVis sg
    leftDistrib     = property $ do
        a       <- rand
        endomPT sg testEq plus (a `times`)
    rightDistrib    = property $ do
        a       <- rand
        endomPT sg testEq plus (`times` a)
    nonzero         = propertyOnce $ do
        annotate $ rShow one
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

fieldProps              :: ShowGen r -> TestRel r -> Field r -> [(PropertyName, Property)]
fieldProps sg testEq    = ringProps sg testEq fieldFlags

moduleProps             :: Bool -> ShowGen r -> Ring r -> ShowGen m -> TestRel m ->
                            Module r m -> [(PropertyName, Property)]
moduleProps isLeftMod sgr@(rShow, _) rR sgm mTestEq mM@(Module { .. })  =
    abelianGroupProps sgm mTestEq ag ++
        [("endM", endM), ("distribM", distribM), ("identityM", identityM), ("assocM", assocM)]
        ++ bDivProps rShow sgm mTestEq mM
  where
    endM            = property $ do
        r       <- genVis sgr
        endomPT sgm mTestEq ag.plus (scale r)
    distribM        = property $ do
        m       <- genVis sgm
        homomPT sgr rR.plus mTestEq ag.plus (`scale` m)
    identityM       = property $
        sameFun1PT sgm mTestEq (scale rR.one) id
    (*~)            = (if isLeftMod then id else flip) rR.times
    assocM          = property $ do
        a       <- genVis sgr
        b       <- genVis sgr
        sameFun1PT sgm mTestEq (scale (a *~ b)) (scale a . scale b)

rModProps               :: ShowGen r -> Ring r -> ShowGen m -> TestRel m ->
                            RMod r m -> [(PropertyName, Property)]
rModProps               = moduleProps True

modRProps               :: ShowGen r -> Ring r -> ShowGen m -> TestRel m ->
                            ModR r m -> [(PropertyName, Property)]
modRProps               = moduleProps False

rAlgProps               :: ShowGen r -> Ring r -> ShowGen a -> TestRel a -> RingFlags ->
                            RAlg r a -> [(PropertyName, Property)]
rAlgProps sgr rR sga aTestEq reqAFlags (RAlg { .. })    =
    ringProps sga aTestEq reqAFlags aR ++ ringHomomProps sgr rR aTestEq aR fromR ++
        [("centerA", centerA), ("scaleA", scaleA)]
  where
    (*~)            = aR.times
    centerA         = property $ do
        r       <- genVis sgr
        let ra  = fromR r
        a       <- genVis sga
        aTestEq (ra *~ a) (a *~ ra)
    scaleA          = property $ do
        r       <- genVis sgr
        let ra  = fromR r
        sameFun1PT sga aTestEq (scale r) (ra *~)


zzExpGen                :: Integer -> Gen Integer
-- ^ @zzExpGen lim@ is an exponential generator with origin 0; @lim@ must be >= 0
zzExpGen lim            = Gen.integral (Range.exponentialFrom 0 (- lim) lim)

zzGen                   :: Gen Integer
zzGen                   = zzExpGen (2 ^ (98 :: Int))

zzShowGen               :: ShowGen Integer
zzShowGen               = (show, zzGen)

zzTestOps               :: TestOps Integer
zzTestOps               = (zzShowGen, (===))

showToShows             :: (a -> String) -> a -> ShowS
showToShows aShow a     = (aShow a ++)

pairTestOps             :: TestOps a -> TestOps b -> TestOps (a, b)
pairTestOps ((aShow, aGen), aTestEq) ((bShow, bGen), bTestEq)   =
    ((pShow, pGen), pTestEq)
  where
    pShow (a, b)    = pairShows (showToShows aShow) (showToShows bShow) (a, b) ""
    pGen            = liftM2 ( , ) aGen bGen
    pTestEq x@(a, b) y@(c, d)   = do
        annotate $ pShow x
        annotate $ pShow y
        aTestEq a c
        bTestEq b d

listShowWith            :: (a -> String) -> [a] -> String
listShowWith aShow as   = showListWith (showToShows aShow) as ""

listShowGen             :: Range Int -> ShowGen a -> ShowGen [a]
listShowGen lenRange (aShow, aGen)  = (listShowWith aShow, Gen.list lenRange aGen)

listTestEq              :: (a -> String) -> TestRel a -> TestRel [a]
listTestEq aShow aTestEq as bs  = do
    annotate $ listShow as
    annotate $ listShow bs
    length as === length bs
    zipWithM_ aTestEq as bs
  where
    listShow        = listShowWith aShow

listTestOps             :: Range Int -> TestOps a -> TestOps [a]
listTestOps lenRange (sga@(aShow, _), aTestEq)  =
    (listShowGen lenRange sga, listTestEq aShow aTestEq)


readsProp               :: ShowGen a -> TestRel a -> ReadS a -> (PropertyName, Property)
readsProp sg@(aShow, _) testEq aReads   = ("read", readShow)
  where
    readShow        = property $ do
        a       <- genVis sg
        let xSs = aReads (aShow a)
            xs  = [x | (x, "") <- xSs]
        annotateShow $ map snd xSs  -- tail string(s) after possible parses
        length xs === 1
        testEq (head xs) a


checkGroup              :: String -> [(PropertyName, Property)] -> IO Bool
checkGroup name props   = checkParallel $ Hh.Group (fromString name) props

checkAll                :: [IO Bool] -> IO Bool
-- ^ like 'Control.Monad.Extra.andM', but doesn't short-circuit (it always runs all the tests),
-- ^    and it prints the results.
checkAll checks         = do    -- liftM and (sequence checks)
    oks         <- sequence checks
    print oks
    pure (and oks)


testAlgebra             :: IO Bool
testAlgebra             =
    checkAll [
        checkGroup "zzRing" $ ringProps zzShowGen (===) integralDomainFlags zzRing,
        checkGroup "Integer order, show/read" $
            totalOrderProps zzShowGen (==) compare ++
                [readsProp zzShowGen (===) reads]
        -- @@ , test more:
    ]
