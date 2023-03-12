{-# LANGUAGE AllowAmbiguousTypes, CPP, Strict, UndecidableInstances #-}

{- |  This module defines the most common types of algebras, and simple functions using them.
    
    An /algebraic structure/ or /algebra/ is a set together with a collection of operations
    (functions) on it that satisfy some specified axioms (identities). Algebras are important
    computationally because working over them allows us to implement an algorithm once, in its
    natural level of generality. We often want to construct or analyze specific algebras, often
    by using other algebras. We implement an algebra using a first-class data value rather than
    a type class, because a single type may admit more than one structure as a given type of
    algebra. (For example, consider quotient algebras such as @ℤ/pℤ@ or @R[X, Y]/(f, g)@ for
    various @p@, @f@, and @g@.) If there are default or standard algebra(s) for a certain data
    type, then one could also provide implicit access to them via type classes.
    
    Note that a set of constructive (e.g. Haskell) values is an attempt to represent a set of
    abstract (mathematical) values. The abstract values have an implicit notion of (abstract)
    equality, but this is not always computable. Equations and terms such as injective,
    surjective, bijective, associative, commutative, distributive, inverse, homomorphism,
    \"there exists\", etc. normally refer to abstract values and abstract equality, since they
    are used in reasoning about program correctness. We say that a constructive function @f@ is
    /well defined/ or /respects abstraction/ if @x = y => f x = f y@ (where @=@ and @=>@
    represent abstract equality and implication). In that case we often use the same name @f@
    to refer to the abstract function that the constructive @f@ implements. We also \"abuse
    notation\" and sometimes use the same name to refer to both an algebra and its underlying
    set.
    
    For more on general algebra, see http://en.wikipedia.org/wiki/Universal_algebra. However,
    note that we use the term \"algebra\" here loosely to allow operations with results of any
    type, so our algebras are not always Omega-algebras. Also, in practice we must sometimes
    use partial functions, inexact approximations, or estimates that have only a (hopefully
    high) probability of being accurate.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~.
-}

module Math.Algebra.General.Algebra (
    -- * Common function types
    -- ** Pred
    assert,
    Pred,
    -- ** Op1
    Op1, pairOp1,
    -- ** Op2
    Op2, pairOp2,
    (.*), on,
    (!$),
    
    -- * Equivalence relations
    -- ** EqRel
    EqRel,
    pairEq, liftEq,
    -- ** Cls
    Cls(..),
    
    -- * Comparison
    -- ** Cmp
    Cmp, ICmp(iCmp), withCmp,
    cmpEq,
    maxBy, minBy,
    lex2Cmp, liftCompare,
    
    -- * Groups
    -- ** MonoidFlags
    show0x, IntBits, (.&.), (.|.), zeroBits, eiBit, eiBits, hasEIBit, hasEIBits,
    MonoidFlag(Abelian, IsGroup), MonoidFlags, agFlags,
    -- ** Group
    Group(..), IGroup(iGroup), gFlags, (==:), (*:), gId, gIsId, gInv, withGroup,
    expt1, (^:), gpExpt, pairGp, pairGp2, gpModF, gpProductL', gpProductR,
    -- ** AbelianGroup
    AbelianGroup, agPlus, agZero, agIsZero, agNeg,
    IAbelianGroup(iAG), (==.), (+.), zero, isZero, neg, withAG,
    (-.), sumL', sumR,
    
    -- * Rings and fields
    -- ** RingFlags
    RingFlag(NotZeroRing, IsCommutativeRing, NoZeroDivisors, IsInversesRing), RingFlags,
    integralDomainFlags, divisionRingFlags, fieldFlags,
    -- ** Ring
    Ring(..), rEq, rPlus, rZero, rIsZero, rNeg,
    IRing(iRing), iRFlags, (*.), one, fromZ, bDiv2, withRing,
    rIsOne, (/.), nearQuo, smallRem, rInv, divides,
    (^.), rExpt, rSumL', rSumR, rProductL', rProductR,
    -- ** Field
    Field, divisionRing, field, fieldGcd,
    
    -- * Modules and R-algebras
    -- ** Module, RMod, ModR
    Module(..), RMod, ModR,
    pairMd, mdModF,
    -- ** RAlg
    RAlg(..),
    algMd,
    
    -- * Basic numeric rings
    numAG,
    -- ** Integer
    zzAG, zzDiv2, zzRing,
    -- ** Double
    dblAG, dblRing,
    
    -- * Converting \<-> String
    pairShows,
    plusS, timesS, quoS,
    Prec, applPrec, exptPrec, multPrec, addPrec, ShowPrec,
    trimStart,
    zzReads, agReads, rngReads, polynomReads
) where

import Control.Exception (assert)
import Data.Bits (Bits, FiniteBits, (.&.), (.|.), bit, finiteBitSize, testBit, zeroBits)
import Data.Char (isDigit)
import Data.Function (on)
import Data.Functor.Classes (liftCompare, liftEq)
import Data.List (foldl', stripPrefix)
import Data.List.Extra (trimStart)
import Data.Maybe (maybeToList)
import Numeric (readDec, showHex)
import Text.ParserCombinators.ReadPrec (Prec)

-- import Data.Constraint {- @@ (...) -} hiding (withDict)
#if __GLASGOW_HASKELL__ >= 904
import GHC.Exts (withDict)
#else
import Unsafe.Coerce (unsafeCoerce)
#endif


#if __GLASGOW_HASKELL__ < 904
withDict        :: forall cls meth r. {- WithDict cls meth => -} meth -> (cls => r) -> r
-- @cls@ must have no superclasses, and exactly one method of type @meth@.
withDict alg k  = unsafeCoerce (Gift k :: Gift cls r) alg

-- | for using an algebra as a typeclass dictionary
newtype Gift cls r  = Gift (cls => r)
#endif

infixr 8    ^., ^:
infixl 7    *., *:, /.
infixl 6    +., -.
infix  4    ==., ==:    -- @@ /=, <, <=, >=, >


-- * Common function types

-- ** Pred

type Pred a     = a -> Bool
-- ^ a predicate

-- ** Op1

type Op1 a      = a -> a
-- ^ a 1-argument operation (function) on @a@

pairOp1         :: (a -> a') -> (b -> b') -> (a, b) -> (a', b')
{- ^ > pairOp1 f g (x, y) = (f x, g y)
    
    Note @pairOp1@'s type specializes to @Op1 a -> Op1 b -> Op1 (a, b)@. -}
pairOp1 f g (x, y)  = (f x, g y)

-- ** Op2

type Op2 a      = a -> a -> a
-- ^ a 2-argument operation (function) on @a@

pairOp2         :: (a -> a' -> a'') -> (b -> b' -> b'') -> (a, b) -> (a', b') -> (a'', b'')
{- ^ > pairOp2 f g (x, y) (u, v) = (f x u, g y v)
    
    Note @pairOp2@'s type specializes to @Op2 a -> Op2 b -> Op2 (a, b)@. -}
pairOp2 f g (x, y) (u, v)   = (f x u, g y v)

(.*)            :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
infixr 9 .*     -- for mixing with @.@
{- ^ > (f .* g) x y = f (g x y)
    
    cf. @(f \`'on'\` g) x y = f (g x) (g y)@ -}
(f .* g) x y    = f (g x y)

(!$)            :: (a -> b) -> a -> b
infixl 1 !$
{- ^ strict function application for functions of more than one argument.
    
    @'(!$)' = '($!)'@ but !$ is @infixl 1@ instead of @infixr 0@. -}
(!$)            = ($!)


-- * Equivalence relations

-- ** EqRel

type EqRel a    = a -> a -> Bool
{- ^ An (abstract) /equivalence relation/ ≡ must be reflexive (@x ≡ x@), symmetric
    (@x ≡ y => y ≡ x@), and transitive (@x ≡ y && y ≡ z => x ≡ z@). An @(EqRel a)@ attempts to
    implement such a relation, but may be only approximate. -}

pairEq          :: EqRel a -> EqRel b -> EqRel (a, b)
-- ^ > pairEq aEq ~bEq (x, ~y) (u, ~v) = aEq x u && bEq y v
pairEq aEq ~bEq (x, ~y) (u, ~v)     = aEq x u && bEq y v

-- ** Cls

newtype Cls a   = Cls { clsRep :: a } deriving (Eq, Show)
{- ^ A value @(Cls r)@ represents the class of elements \"equivalent\" to @r@ (according to a
    specified equivalence relation). Usually we require @r@ to be \"simple\" or \"normalized\"
    in some way. -}


-- * Comparison

-- ** Cmp

type Cmp a      = a -> a -> Ordering
{- ^ A @(Cmp a)@ must be antisymmetric (@cmp a b@ is always the opposite of @cmp b a@) and
    transitive (@a \<= b and b \<= c => a \<= c@). Then >=, ==, \<, and > are also transitive;
    @a \<= b and b \< c => a \< c@; @a == b and b \< c => a \< c@; etc.; where e.g. @a == b@
    here means @cmp a b == EQ@.
    
    Also, this @==@ is an equivalence relation. If @==@ agrees with abstract equality, then
    @cmp@ is a /total order/. -}

{- | An @(ICmp a)@ is implicitly a 'Cmp', given by 'iCmp'. -}
class ICmp a where
    iCmp        :: Cmp a

withCmp         :: forall a r. Cmp a -> (ICmp a => r) -> r
-- ^ Use a @(Cmp a)@ as an @(ICmp a)@.
withCmp         = withDict @(ICmp a)

cmpEq           :: Cmp a -> EqRel a
-- ^ > cmpEq cmp x y = cmp x y == EQ
cmpEq cmp x y   = cmp x y == EQ

maxBy           :: Cmp a -> Op2 a
-- ^ > maxBy cmp x y = if cmp x y /= GT then y else x
maxBy cmp x y   = if cmp x y /= GT then y else x

minBy           :: Cmp a -> Op2 a
-- ^ > minBy cmp x y = if cmp x y /= GT then x else y
minBy cmp x y   = if cmp x y /= GT then x else y

lex2Cmp         :: Cmp a -> Cmp b -> Cmp (a, b)
-- ^ lexicographic comparison; the @Cmp (a, b)@ returns the first non-EQ result
lex2Cmp aCmp ~bCmp (x, ~y) (u, ~v)  = let d = aCmp x u in if d /= EQ then d else bCmp y v


-- * Groups

-- ** MonoidFlags

show0x          :: (Integral a, Show a) => a -> String
-- ^ shows with a "0x" prefix; the argument must be nonnegative
show0x n        = "0x" ++ showHex n ""

newtype IntBits e   = IntBits Int
    deriving (Eq, Bits, FiniteBits)
-- ^ a set of @e@s. @|e| \<= finiteBitSize (0 :: Int)@.

instance Show (IntBits e) where     -- e.g. for testing & debugging
    show (IntBits n)    = show0x n

eiBit           :: forall e. (Enum e, Bounded e) => e -> IntBits e
-- ^ a singleton set
eiBit e         =
    assert (fromEnum (maxBound :: e) < finiteBitSize (0 :: Int)) (bit (fromEnum e))

eiBits          :: (Enum e, Bounded e) => [e] -> IntBits e
eiBits es       = foldl' (.|.) zeroBits (map eiBit es)

hasEIBit        :: Enum e => IntBits e -> e -> Bool
hasEIBit bs e   = testBit bs (fromEnum e)

hasEIBits       :: IntBits e -> IntBits e -> Bool
-- ^ @hasEIBits bs req@ tests whether all the bits of @req@ are in @bs@
hasEIBits bs req    = bs .&. req == req

data MonoidFlag =
          Abelian           -- ^ => @op@ is commutative
        | IsGroup           -- ^ => all elements have inverses
    deriving (Enum, Bounded)
-- ^ a single (1-bit or boolean) property of a 'Group'

type MonoidFlags    = IntBits MonoidFlag

agFlags             :: MonoidFlags
agFlags             = eiBits [Abelian, IsGroup]

-- ** Group

{- | A @(Group flags eq op ident isIdent inv)@ must satisfy the axioms below. This generalizes
    the notion of a set of composable symmetries (such as translation, rotation, reflection,
    scaling, etc.). -}
data Group g    = Group {
    gpFlags :: MonoidFlags,
    gpEq    :: EqRel g,     -- ^ @eq x y@ must imply abstract equality @x = y@
    gpOp    :: Op2 g,       -- ^ @op@ is well defined and associative
    gpId    :: g,           -- ^ @(ident \`op\`) = (\`op\` ident) = id@
    gpIsId  :: Pred g,      -- ^ @isIdent x = ident \`eq\` x@ for all @x@
    gpInv   :: Op1 g        -- ^ @(inv x) \`op\` x = x \`op\` (inv x) = ident@ for all @x@;
        -- therefore @inv@ is well defined also
}
{- ^ A /homomorphism of groups/ is a well defined function @f :: G -> G'@ that satisfies
    @f (op x y) = op' (f x) (f y)@. This implies @f ident = ident'@, and
    @f (inv x) = inv' (f x)@. -}

{- | An @(IGroup a)@ is implicitly a 'Group', given by 'iGroup'. -}
class IGroup a where
    iGroup      :: Group a

gFlags          :: forall a. IGroup a => MonoidFlags
-- ^ @gFlags = gpFlags (iGroup @a)@
gFlags          = gpFlags (iGroup @a)
(==:)           :: IGroup a => EqRel a
-- ^ @(==:) = gpEq iGroup@
(==:)           = gpEq iGroup
(*:)            :: IGroup a => Op2 a
-- ^ @(*:) = gpOp iGroup@
(*:)            = gpOp iGroup
gId             :: IGroup a => a
-- ^ @gId = gpId iGroup@
gId             = gpId iGroup
gIsId           :: IGroup a => Pred a
-- ^ @gIsId = gpIsId iGroup@
gIsId           = gpIsId iGroup
gInv            :: IGroup a => Op1 a
-- ^ @gInv = gpInv iGroup@
gInv            = gpInv iGroup

withGroup       :: forall a r. Group a -> (IGroup a => r) -> r
-- ^ Use a @(Group a)@ as an @(IGroup a)@.
withGroup       = withDict @(IGroup a)

expt1           :: Integral b => Op2 a -> a -> b -> a
-- ^ exponentiation to an integral power \>= 1
expt1 (*~) x n
    | n == 1    = x
    | odd n     = x *~ expt1 (*~) x (n - 1)
    | otherwise = assert (n > 1) $ expt1 (*~) (x *~ x) (n `quot` 2)
{-# SPECIALIZE expt1 :: Op2 a -> a -> Int -> a #-}

(^:)            :: (IGroup a, Integral b) => a -> b -> a
-- ^ exponentiation to an integral power
(^:) x n
    | n > 0     = expt1 (*:) x n
    | n == 0    = gId
    | otherwise = gInv (x ^: (- n))
{-# SPECIALIZE (^:) :: IGroup a => a -> Int -> a #-}

gpExpt          :: Integral b => Group a -> a -> b -> a
-- ^ exponentiation to an integral power, using a 'Group' passed explicitly
gpExpt gp       = withGroup gp (^:)

pairGp          :: forall a b. (IGroup a, IGroup b) => Group (a, b)
-- ^ direct product of two groups
pairGp          =
    Group (gFlags @a .&. gFlags @b)
          (pairEq (==:) (==:))
          (pairOp2 (*:) (*:))
          (gId, gId)
          (\ (a, ~b) -> gIsId a && gIsId b)
          (pairOp1 gInv gInv)

pairGp2         :: Group a -> Group b -> Group (a, b)
-- ^ for passing explicit 'Group'(s) to 'pairGp'
pairGp2 aGp bGp = withGroup aGp (withGroup bGp pairGp)

gpModF          :: Group g -> Op1 g -> MonoidFlags -> Group (Cls g)
-- ^ @gpModF gp reduce@ is @gp@ modulo a normal subgroup, using @reduce@ to produce @Cls@
-- (coset) representatives.
gpModF (Group flags eq op ident isIdent inv) reduce extraFlags  =
    let modF    = Cls . reduce
        redId   = reduce ident
    in  Group (flags .|. extraFlags)
            (eq `on` clsRep) (modF .* (op `on` clsRep)) (Cls redId)
            ((if isIdent redId then isIdent else eq redId) . clsRep)
            (modF . inv . clsRep)

gpProductL'     :: Group g -> [g] -> g
-- ^ product using foldl'
gpProductL' Group{ gpOp, gpId }     = foldl' gpOp gpId

gpProductR      :: Group g -> [g] -> g
-- ^ product using foldr
gpProductR Group{ gpOp, gpId }      = foldr gpOp gpId

-- ** AbelianGroup

type AbelianGroup       = Group
{- ^ @op@ must be commutative. We then usually use additive notation, as in the next few
    functions. -}
agPlus          :: AbelianGroup a -> Op2 a
-- ^ 'agPlus' = 'gpOp'
agPlus          = gpOp
agZero          :: AbelianGroup a -> a
-- ^ 'agZero' = 'gpId'
agZero          = gpId
agIsZero        :: AbelianGroup a -> Pred a
-- ^ 'agIsZero' = 'gpIsId'
agIsZero        = gpIsId
agNeg           :: AbelianGroup a -> Op1 a
-- ^ 'agNeg' = 'gpInv'
agNeg           = gpInv

{- | An @(IAbelianGroup a)@ is implicitly an 'AbelianGroup', given by 'iAG'. -}
class IAbelianGroup a where
    iAG         :: AbelianGroup a

(==.)           :: IAbelianGroup a => EqRel a
-- ^ @(==.) = gpEq iAG@
(==.)           = gpEq iAG
(+.)            :: IAbelianGroup a => Op2 a
-- ^ @(+.) = agPlus iAG@
(+.)            = agPlus iAG
zero            :: IAbelianGroup a => a
-- ^ @zero = agZero iAG@
zero            = agZero iAG
isZero          :: IAbelianGroup a => Pred a
-- ^ @isZero = agIsZero iAG@
isZero          = agIsZero iAG
neg             :: IAbelianGroup a => Op1 a
-- ^ @neg = agNeg iAG@
neg             = agNeg iAG

withAG          :: forall a r. AbelianGroup a -> (IAbelianGroup a => r) -> r
-- ^ Use an @(AbelianGroup a)@ as an @(IAbelianGroup a)@.
withAG          = withDict @(IAbelianGroup a)

(-.)            :: IAbelianGroup a => Op2 a
-- ^ @x -. y = x +. neg y@
x -. y          = x +. neg y

sumL'           :: IAbelianGroup a => [a] -> a
-- ^ sum using foldl'
sumL'           = gpProductL' iAG

sumR            :: IAbelianGroup a => [a] -> a
-- ^ sum using foldr
sumR            = gpProductR iAG


-- * Rings and fields

-- ** RingFlags

data RingFlag   =
          NotZeroRing       -- ^ => 0 \/= 1
        | IsCommutativeRing -- ^ => multiplication is commutative
        | NoZeroDivisors    -- ^ => (ab == 0 => a == 0 or b == 0)
        | IsInversesRing    -- ^ => every nonzero element has a multiplicative inverse
    deriving (Enum, Bounded)
-- ^ a single (1-bit or boolean) property of a 'Ring'

type RingFlags  = IntBits RingFlag

integralDomainFlags :: RingFlags
-- ^ a commutative ring with 0 \/= 1 and no zero divisors
integralDomainFlags = eiBits [NotZeroRing, IsCommutativeRing, NoZeroDivisors]

divisionRingFlags   :: RingFlags
-- ^ 0 \/= 1 and every nonzero element has a multiplicative inverse
divisionRingFlags   = eiBits [NotZeroRing, NoZeroDivisors, IsInversesRing]

fieldFlags          :: RingFlags
-- ^ a commutative division ring
fieldFlags          = divisionRingFlags .|. eiBit IsCommutativeRing

-- ** Ring

{- | A @(Ring ag (*~) one' fromZ' bDiv2')@ must satisfy the axioms below. Examples include the
    integers ℤ, and other rings of algebraic numbers, polynomials, n x n matrices, etc. -}
data Ring a     = Ring {
    rAG     :: AbelianGroup a,
    rFlags  :: RingFlags,
    rTimes  :: Op2 a,       -- ^ @(*.)@ is well defined, distributes over @plus@, and is
        -- normally associative
    rOne    :: a,           -- ^ @(one *.) = (*. one) = id@
    rFromZ  :: Integer -> a,    -- ^ the unique ring homomorphism from Z to this ring
    rBDiv2  :: Bool -> a -> a -> (a, a)     {- ^ @bDiv2 doFull y m = (q, r) => y = m*q + r@ and
        @r@'s \"size\" is (attempted to be) minimized. If @doFull@, then all of @r@ is
        minimized; else just its \"topmost\" nonzero \"term\" is. (Words such as \"size\" have
        meanings that vary by context. Also in general, the results of @bDiv2@ may not be
        uniquely determined by these requirements.) -}
}
-- ^ A ring is /commutative/ if @*.@ is. A /unit/ is an element @x@ such that there exists a
-- @y@ with @x *. y = y *. x = one@.
--
-- A /homomorphism of rings/ @f :: R -> R'@ is an additive (Abelian group) homomorphism that
-- also satisfies @f (x *. y) = f x *. f y@ and @f one = one'@.

rEq             :: Ring a -> EqRel a
-- ^ > rEq = gpEq . rAG
rEq             = gpEq . rAG
rPlus           :: Ring a -> Op2 a
-- ^ > rPlus = agPlus . rAG
rPlus           = agPlus . rAG
rZero           :: Ring a -> a
-- ^ > rZero = agZero . rAG
rZero           = agZero . rAG
rIsZero         :: Ring a -> Pred a
-- ^ > rIsZero = agIsZero . rAG
rIsZero         = agIsZero . rAG
rNeg            :: Ring a -> Op1 a
-- ^ > rNeg = agNeg . rAG
rNeg            = agNeg . rAG

{- | An @(IRing a)@ is implicitly a 'Ring', given by 'iRing'. -}
class IRing a where
    iRing       :: Ring a
instance {-# INCOHERENT #-} IRing a => IAbelianGroup a where
    iAG         = rAG iRing

iRFlags         :: forall a. IRing a => RingFlags
-- ^ @iRFlags  = rFlags (iRing @a)@
iRFlags         = rFlags (iRing @a)
(*.)            :: IRing a => Op2 a
-- ^ @(*.) = rTimes iRing@
(*.)            = rTimes iRing
one             :: IRing a => a
-- ^ @one = rOne iRing@
one             = rOne iRing
fromZ           :: IRing a => Integer -> a
-- ^ @fromZ = rFromZ iRing@
fromZ           = rFromZ iRing
bDiv2           :: IRing a => Bool -> a -> a -> (a, a)
-- ^ @bDiv2 = rBDiv2 iRing@
bDiv2           = rBDiv2 iRing

withRing        :: forall a t. Ring a -> (IRing a => t) -> t
-- ^ Use a @(Ring a)@ as an @(IRing a)@.
withRing        = withDict @(IRing a)

rIsOne          :: Ring a -> Pred a
-- ^ > rIsOne aR = rEq aR (rOne aR)
rIsOne aR       = rEq aR (rOne aR)

(/.)            :: IRing a => Op2 a
-- ^ exact quotient, i.e. division (@bDiv2 False@) should have zero remainder
y /. m          =
    let (q, r)      = bDiv2 False y m
    in  if isZero r then q else error "division is not exact"

nearQuo                 :: Ring a -> Bool -> Op2 a
-- ^ > nearQuo rR doFull y m = fst (rBDiv2 rR doFull y m)
nearQuo rR doFull y m   = fst (rBDiv2 rR doFull y m)
smallRem                :: Ring a -> Bool -> Op2 a
-- ^ > smallRem rR doFull y m = snd (rBDiv2 rR doFull y m)
smallRem rR doFull y m  = snd (rBDiv2 rR doFull y m)

rInv            :: IRing a => Op1 a
-- ^ > rInv = (one /.)
rInv            = (one /.)

divides         :: IRing a => a -> a -> Bool
-- ^ whether an element divides another element; note the arguments are reversed from division
divides d y     = isZero (snd (bDiv2 False y d))

(^.)            :: (IRing a, Integral b) => a -> b -> a
-- ^ exponentiation to an integral power
(^.) x n
    | n > 0     = expt1 (*.) x n
    | n == 0    = one
    | otherwise = rInv (x ^. (- n))
{-# SPECIALIZE (^.) :: IRing a => a -> Int -> a #-}

rExpt           :: Integral b => Ring a -> a -> b -> a
-- ^ exponentiation to an integral power, using a 'Ring' passed explicitly
rExpt aR        = withRing aR (^.)

rSumL'          :: Ring a -> [a] -> a
-- ^ sum using foldl'
rSumL' aR       = withAG (rAG aR) sumL'

rSumR           :: Ring a -> [a] -> a
-- ^ sum using foldr
rSumR aR        = withAG (rAG aR) sumR

rProductL'      :: Ring g -> [g] -> g
-- ^ product using foldl'
rProductL' Ring{ rTimes, rOne }     = foldl' rTimes rOne

rProductR       :: Ring g -> [g] -> g
-- ^ product using foldr
rProductR Ring{ rTimes, rOne }      = foldr rTimes rOne

-- ** Field

type Field      = Ring
{- ^ A /division ring/ is a ring with @zero \/= one@ and in which every non-zero element is a
    unit. A /field/ is a commutative division ring. -}

divisionRing    :: AbelianGroup a -> RingFlags -> Op2 a -> a -> (Integer -> a) -> Op1 a ->
                    Ring a
-- ^ @divisionRing ag extraFlags (*~) one' fromZ' inv@ creates a division ring
divisionRing ag extraFlags (*~) one' fromZ' inv     =
    let zero'       = agZero ag
        bDiv2' _ y m    = if agIsZero ag m then (zero', y) else (inv m *~ y, zero')
    in  Ring ag (divisionRingFlags .|. extraFlags) (*~) one' fromZ' bDiv2'

field           :: AbelianGroup a -> Op2 a -> a -> (Integer -> a) -> Op1 a -> Field a
-- ^ @field ag (*~) one' fromZ' inv@ creates a 'Field'
field ag        = divisionRing ag fieldFlags

fieldGcd        :: Field a -> Op2 a
-- ^ creates a gcd (greatest common divisior) function for a 'Field'
fieldGcd (Ring ag _ _ one' _ _) x y = if agIsZero ag x && agIsZero ag y then agZero ag else one'


-- * Modules and R-algebras

-- ** Module, RMod, ModR

{- | Given an Abelian group G, End(G) = { endomorphisms of G } = { homomorphisms G -> G } is
    a ring, with @*.@ given by composition. Given a ring R, a /left module over R/ is an
    Abelian group M together with a ring homomorphism R -> End(M). A /right module over R/
    has the same definition, but with function composition defined on the right, i.e. by
    @(flip .)@. A /module/ is either a left module or a right module. -}
data Module r m = Module { mdAG :: AbelianGroup m, mdScale :: r -> Op1 m }
{- ^ A /vector space/ is a module over a field.

    A /homomorphism of R-modules/ or /R-linear map/ @f :: M -> M'@ is an additive homomorphism
    that also satisfies @f (r \`scale\` m) = r \`scale\` f m@. -}

type RMod       = Module
-- ^ a left module over R
type ModR       = Module
-- ^ a right module over R

pairMd          :: Module r a -> Module r b -> Module r (a, b)
-- ^ direct sum (or product) of two modules
pairMd aMd bMd  =
    Module (pairGp2 (mdAG aMd) (mdAG bMd)) (\r -> pairOp1 (mdScale aMd r) (mdScale bMd r))

mdModF          :: Module r a -> Op1 a -> Module r (Cls a)
{- ^ @mdModF md reduce@ is @md@ modulo a submodule, using @reduce@ to produce @Cls@ (coset)
    representatives. -}
mdModF (Module ag scale) reduce     =
    let modF    = Cls . reduce
    in  Module (gpModF ag reduce zeroBits) (\ r (Cls m) -> modF (scale r m))

-- ** RAlg

{- | Given a commutative ring @R@, an /R-algebra/ is a ring @A@ together with a ring
    homomorphism @R -> center(A)@. (The /center/ of a group or ring is the set of elements that
    commute with every element of the group or ring.) This makes @A@ into an @R-module@. -}
data RAlg r a   = RAlg {
    algRing     :: Ring a,
    algScale    :: r -> Op1 a,
    algFromR    :: r -> a
}

algMd           :: RAlg r a -> Module r a
-- ^ > algMd (RAlg aRing scale _) = Module (rAG aRing) scale
algMd (RAlg aRing scale _)      = Module (rAG aRing) scale


-- * Basic numeric rings

numAG           :: (Eq n, Num n) => AbelianGroup n
-- ^ @n@ under addition
numAG           = Group agFlags (==) (+) 0 (== 0) negate

-- ** Integer

zzAG            :: AbelianGroup Integer
-- ^ the integers ℤ under addition
zzAG            = numAG

zzDiv2          :: Bool -> Integer -> Integer -> (Integer, Integer)
-- ^ integer division, rounding toward 0
zzDiv2 _ n d
    | d == 0    = (0, n)
    | d < 0     = let (q, r) = zzDiv2 False n (- d) in (- q, r)
    | otherwise = let (q, r) = divMod n d
                  in  if 2*r < d then (q, r) else (q + 1, r - d)

zzRing          :: Ring Integer
-- ^ the ring of integers ℤ
zzRing          = Ring zzAG integralDomainFlags (*) 1 id zzDiv2

instance IRing Integer where
    iRing       = zzRing

-- ** Double

dblAG           :: AbelianGroup Double
-- ^ Double precision numbers under addition
dblAG           = numAG

dblRing         :: Field Double
-- ^ the approximate field of Doubles
dblRing         = field dblAG (*) 1 fromInteger recip


-- * Converting \<-> String

pairShows               :: (a -> ShowS) -> (b -> ShowS) -> (a, b) -> ShowS
pairShows aShows bShows (a, b) t    = '(' : aShows a (',' : bShows b (')' : t))


plusS           :: String -> String -> String
{- ^ @plusS s t@ shows the sum @s+t@. The caller checks precedences and parenthesizes @s@
    and/or @t@ if necessary. @plusS@ checks for @s@ or @t@ being 0, or @t@ being negative. -}
plusS s t       = if s == "0" then t else case t of
    "0"         -> s
    '-':_       -> s ++ t
    _           -> s ++ '+' : t

timesS          :: String -> String -> String
{- ^ @timesS s t@ shows the product @st@. The caller checks precedences and parenthesizes @s@
    and/or @t@ if necessary. @timesS@ checks for @s@ or @t@ being 1, @t@ being empty, or
    @s@ being -1. -}
timesS s t
    | null t || t == "1"    = s
    | s == "1"              = t
    -- | s == "0" || t == "0"  = "0"
    | s == "-1"             = '-' : t
    | otherwise             = s ++ t

quoS            :: String -> String -> String
{- ^ @quoS s t@ shows the quotient @s/t@. The caller checks precedences and parenthesizes @s@
    and/or @t@ if necessary. @quoS@ checks for @t@ being 1 or @s@ being 0. -}
quoS s t        = if t == "1" || s == "0" then s else s ++ '/' : t


applPrec        :: Prec
-- ^ precedence of function application
applPrec        = 10
exptPrec        :: Prec
-- ^ precedence of exponentiation
exptPrec        = 8
multPrec        :: Prec
-- ^ precedence of multiplication
multPrec        = 7
addPrec         :: Prec
-- ^ precedence of addition
addPrec         = 6

type ShowPrec a = Prec -> a -> String
{- ^ a function to show a value at a given minimum precedence. That is, the result is
    parenthesized if its top operator has less than the given precedence. -}


zzReads         :: ReadS Integer
-- ^ avoid using just @reads@ so e.g. @zzReads "2e+1" = [(2, "e+1")]@
zzReads s       = case trimStart s of
    '-':t   -> [(- n, u) | (n, u) <- readDec (trimStart t)]
    t       -> readDec t

agReads         :: forall g. IAbelianGroup g => ReadS g -> ReadS g
-- ^ read a possible sum of terms or \"-\" terms, given a function to read a single term
agReads termReads   =
    let sumReads            :: Maybe g -> ReadS g   -- result is mg followed by s
        sumReads mg s       = case trimStart s of
                                '-':t   -> reads1 mg neg t
                                '+':t   -> reads1 mg id t
                                _       -> maybe (reads1 mg id s) (\ g -> [(g, s)]) mg
        reads1              :: Maybe g -> Op1 g -> ReadS g  -- mg + (f(next term) + rest of s)
        reads1 mg f s       = [(maybe y (y +.) mg, u)
                              | (x, t) <- termReads s,
                                (y, u) <- sumReads (Just (f x)) t]
    in  sumReads Nothing      -- right-associative sum for efficiency in common cases

rngReads        :: forall r. IRing r => ReadS r -> ReadS r
{- ^ read a ring element as a sum of products or quotients of powers of \"atom\"s, given a
    function to read an \"atom\" -}
rngReads atomReads  =
    let rReads, power       :: ReadS r
        rReads      = agReads termReads
        power s     = do
            let t = trimStart s
            (base, u) <- case t of
                '(':_   -> readParen True rReads t
                _       -> atomReads t
            case trimStart u of
                '^':v   -> [(base ^. e, w) | (e, w) <- zzReads v]
                v       -> [(base, v)]
        product2            :: (r, String) -> [(r, String)]
        product2 (r, s)     =
            case trimStart s of
                '/':u   -> concatMap (\(d, v) -> product2 (r /. d, v)) (power u)
                u       -> case power u of
                            []  -> [(r, u)]
                            pvs -> concatMap (\(d, v) -> product2 (r *. d, v)) pvs
        termReads s = concatMap product2 (power s)
    in  rReads

polynomReads    :: IRing p => [(String, p)] -> ReadS p
-- ^ read a polynomial, given a list of variables. Each variable must have precedence > '^'.
polynomReads varSRs     =
    let digitsOrVarReads s  =
            let s' = trimStart s
            in  case s' of
                c:_     | isDigit c     -> [(fromZ n, t) | (n, t) <- zzReads s']
                _                       -> [(var, t)
                    | (varS, var) <- varSRs,
                      t <- maybeToList (stripPrefix varS s'),
                      null t || not (isDigit (head t))]
    in  rngReads digitsOrVarReads
