{-# LANGUAGE CPP, DataKinds, Strict, ViewPatterns #-}

{- |  This module defines the most common types of algebras, and simple functions using them.
    
    An /algebraic structure/ or /algebra/ is a set together with a collection of operations
    (functions) on it that satisfy some specified axioms (identities). Algebras are important
    computationally because working over them allows us to implement an algorithm once, in its
    natural level of generality. We often want to construct or analyze specific algebras, often
    by using other algebras. We implement an algebra using a first-class data value rather than
    a type class, because a single type may admit more than one structure as a given type of
    algebra. (For example, consider quotient algebras such as @ℤ/pℤ@ or @R[X, Y]/(f, g)@ for
    various dynamically computed @p@, @f@, and @g@.) Also, treating algebras as first-class
    values allows us to construct them at arbitrary times in arbitrary ways. On the other hand,
    type classes are necessary if inlining is desired, e.g. for primitive types.
    
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
    
    This module uses LANGUAGE Strict. This is important both for parallelism, and more general
    efficiency of algebraic code. In particular, except for re-exports, constructor fields and
    function arguments are strict unless marked with a ~. Pairs are usually strict. We also
    always use dot notation for records (OverloadedRecordDot and NoFieldSelectors).
-}

module Math.Algebra.General.Algebra (
    -- * Common function types
    -- ** Pred
    Pred,
    -- ** Op1
    Op1,
    -- ** Op2
    Op2, pairOp2,
    (.*), on,
    (!$),
    
    -- * Equivalence relations
    -- ** EqRel
    EqRel,
    -- ** Cls
    Cls(Cls, rep),
    
    -- * Comparison
    -- ** Cmp
    Cmp,
    cmpEq,
    maxBy, minBy,
    
    -- * Monoids and Groups
    -- $monoids
    -- ** MonoidFlags
    MonoidFlags(MonoidFlags, nontrivial, abelian, isGroup), flagsContain,
    IsNontrivial(..), agFlags,
    -- ** MonoidOps, Group
    MonoidOps(MkMonoid, monFlags, eq, op, ident, isIdent, inv,
        AbelianGroup, plus, zero, isZero, neg),
    Group, expt1, gpExpt, pairMon, gpModF, monProductL', monProductR,
    -- ** AbelianGroup
    AbelianGroup, minus, sumL', sumR,
    
    -- * Rings and fields
    -- $rings
    -- ** RingFlags
    RingFlags(RingFlags, commutative, noZeroDivisors, nzInverses),
    integralDomainFlags, divisionRingFlags, fieldFlags,
    -- ** Ring
    IsDeep(IsDeep, b),
    Ring(Ring, ag, rFlags, times, one, fromZ, bDiv),
    rIsOne, exactQuo, nearQuo, smallRem, rInv, divides,
    rExpt, rSumL', rSumR, rProductL', rProductR,
    -- ** Field
    Field, divisionRing, field, fieldGcd,
    
    -- * Modules and R-algebras
    -- ** Module, RMod, ModR
    Module(Module, ag, scale, bDiv), IsLeftMod(IsLeftMod, b), RMod, ModR,
    pairMd, mdModF,
    -- ** RAlg
    RAlg(RAlg, aR, scale, fromR),
    algMd,
    
    -- * Basic numeric rings
    numAG, numRing,
    -- ** Integer
    zzAG, zzDiv, zzRing,
    -- ** Double
    dblAG, dblRing,
    
    -- * Converting -> Text
    show0x, Text, showT,
    -- ** With Precedence
    Prec(..), PrecText(PrecText, prec, t), parensIf, ensurePrec,
        infixLPT, infixRPT, infixAssocPT, infixPT, infixListPT, fencePT,
        plusPT, sumPT, timesPT, productPT, exptPT,
    ShowPrec, integralPT, zzShowPrec, hex0xPT, integralPowPT, sPairShowPrec, listShowPrec,
        gensShowPrec,
    
    -- * Parsing
    Parser, spaceConsumer, parse, parseAllOrErr,
    pInfixL, pParens, zzParse, agParse, rngParse, zzGensRingParse,
    
    -- * Variable names
    numVarPT, alphaNumVarNames, varNameParse, varParse,
    
    -- * Re-exports
#if ! MIN_VERSION_base(4, 20, 0)
    foldl',
#endif
#if ! MIN_VERSION_base(4, 18, 0)
    liftA2,
#endif
    assert
) where

import GHC.Records

#if ! MIN_VERSION_base(4, 18, 0)
import Control.Applicative (liftA2)     -- unnecesary in base 4.18+, since in Prelude
#endif
import Control.Exception (assert)
import Data.Bifunctor (bimap, second)
import Data.Char (isDigit)
#if ! MIN_VERSION_base(4, 20, 0)
import Data.Foldable (foldl')           -- unnecesary in base 4.20+, since in Prelude
#endif
import Data.Foldable (toList)
import Data.Function (on)
import Data.Functor (($>))
import Data.Functor.Classes (liftEq2)
import Data.Maybe (fromMaybe)
import Data.Strict.Tuple ((:!:), pattern (:!:))
import qualified Data.Text as T
import Data.Text (Text)
import Data.Void (Void)
import Fmt (Buildable, (+|), (|+), build)
import Numeric (showHex)
import Text.Megaparsec (Parsec, (<|>), (<?>), between, eof, errorBundlePretty, many,
    notFollowedBy, parse)
import Text.Megaparsec.Char (digitChar, letterChar, space1)
import Text.Megaparsec.Char.Lexer as L


-- * Common function types

-- ** Pred

type Pred a     = a -> Bool
-- ^ a predicate

-- ** Op1

type Op1 a      = a -> a
-- ^ a 1-argument operation (function) on @(a)@.

-- ** Op2

type Op2 a      = a -> a -> a
-- ^ a 2-argument operation (function) on @(a)@.

pairOp2         :: (a -> a' -> a'') -> (b -> b' -> b'') -> a :!: b -> a' :!: b' -> a'' :!: b''
{- ^ > pairOp2 f g (x :!: y) (u :!: v) = (f x u :!: g y v)
    
    Note 'pairOp2'\'s type specializes to (includes) @Op2 a -> Op2 b -> Op2 (a :!: b)@.
    
    'pairOp2' is like 'bimap', but for functions of 2 arguments. -}
pairOp2 f g (x :!: y) (u :!: v)     = f x u :!: g y v

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
    implement such a relation, but may be only approximate.
    
    'Data.Functor.Classes.liftEq' and 'liftEq2' may be useful when creating an 'EqRel'. -}

-- ** Cls

newtype Cls a   = Cls { rep :: a }  deriving (Eq, Show)
{- ^ A value @(Cls r)@ represents the class of elements \"equivalent\" to @r@ (according to a
    specified equivalence relation). Usually we require @r@ to be \"simple\" or \"normalized\"
    in some way. -}


-- * Comparison

-- ** Cmp

type Cmp a      = a -> a -> Ordering
{- ^ A @(Cmp a)@ must be antisymmetric (@cmp x y@ is always the opposite of @cmp y x@) and
    transitive (@x \<= y and y \<= z => x \<= z@). Then >=, ==, \<, and > are also transitive;
    @x \<= y and y \< z => x \< z@; @x == y and y \< z => x \< z@; etc.; where e.g. @x == y@
    here means @cmp x y == EQ@.
    
    Also, this @==@ is an equivalence relation. If @==@ agrees with abstract equality, then
    @cmp@ is a /total order/.
    
    'Data.Functor.Classes.liftCompare' and 'Data.Functor.Classes.liftCompare2' may be useful
    when creating a 'Cmp'. For lists and pairs, they use lexicographic order: the resulting
    'Cmp' function returns the first non-@EQ@ result when comparing its arguments
    component-wise, else @EQ@. -}

cmpEq           :: Cmp a -> EqRel a
-- ^ > cmpEq cmp x y = cmp x y == EQ
cmpEq cmp x y   = cmp x y == EQ

maxBy           :: Cmp a -> Op2 a
-- ^ > maxBy cmp x y = if cmp x y /= GT then y else x
maxBy cmp x y   = if cmp x y /= GT then y else x

minBy           :: Cmp a -> Op2 a
-- ^ > minBy cmp x y = if cmp x y /= GT then x else y
minBy cmp x y   = if cmp x y /= GT then x else y


-- * Monoids and Groups

{- $monoids
    Abstractly, a /monoid/ is a set, together with an associative operation with identity. If
    there are more elements than just the identity, the monoid is /nontrivial/. If the operation
    is commutative, the monoid is /abelian/. If every element has a (two-sided) inverse, the
    monoid is a /group/. -}

-- ** MonoidFlags

data MonoidFlags        = MonoidFlags {
        nontrivial  :: Bool,    -- ^ \=> more than 1 element
        abelian     :: Bool,    -- ^ \=> @op@ is commutative
        isGroup     :: Bool     -- ^ \=> all elements have inverses, and 'inv' computes them
    } deriving (Eq, Show)
-- ^ known properties of a 'MonoidOps' or 'Group'

instance Semigroup MonoidFlags where
    x <> y      = MonoidFlags {
            nontrivial  = x.nontrivial  || y.nontrivial,
            abelian     = x.abelian || y.abelian,
            isGroup     = x.isGroup || y.isGroup
        }
-- ^ @(\<>)@ is @(||)@ applied to each property

flagsContain    :: (Eq f, Semigroup f) => f -> f -> Bool
-- ^ whether the @True@ properties of the first argument contain those of the second
flagsContain x y    = x <> y == x

newtype IsNontrivial    = IsNontrivial { b :: Bool }
-- ^ whether something is nontrivial, e.g. whether a monoid has more than one element

agFlags             :: IsNontrivial -> MonoidFlags
-- ^ v'MonoidFlags' for an t'AbelianGroup'
agFlags isNontriv   = MonoidFlags { nontrivial = isNontriv.b, abelian = True, isGroup = True }

-- ** MonoidOps, Group

{- | Operations for a monoid. (We use the name 'MonoidOps' instead of 'Monoid' because
    the latter is already used for a type class.) The operations must satisfy the axioms below.
    Note though that 'inv' may be a partial function (defined only for some inputs). -}
data MonoidOps g    = MkMonoid {
    monFlags    :: MonoidFlags,
    eq          :: EqRel g,     -- ^ @eq x y@ must imply abstract equality @x = y@
    op          :: Op2 g,       -- ^ @op@ is well defined and associative
    ident       :: g,           -- ^ @(ident \`op\`) = (\`op\` ident) = id@
    isIdent     :: Pred g,      -- ^ @isIdent x = ident \`eq\` x@ for all @x@
    inv         :: Op1 g        -- ^ @(inv x) \`op\` x = x \`op\` (inv x) = ident@ where
        -- @(inv x)@ is defined; therefore @inv@ is well defined also (where it is defined)
}
{- ^ A /homomorphism of monoids/ is a well defined function @f :: G -> G'@ that satisfies
    @f (op x y) = op' (f x) (f y)@ and @f ident = ident'@. -}

type Group  = MonoidOps
{- ^ A 'Group' is a monoid where 'isGroup' is True, i.e. all elements have inverses, and 'inv'
    is a total function (defined for all inputs) that computes them. 'Group' generalizes the
    notion of a set of composable symmetries (such as translation, rotation, reflection,
    scaling, etc.).
    
    A /homomorphism of groups/ is a well defined function @f :: G -> G'@ that satisfies
    @f (op x y) = op' (f x) (f y)@. This implies @f ident = ident'@, and
    @f (inv x) = inv' (f x)@. -}

expt1           :: Integral b => Op2 a -> a -> b -> a
-- ^ exponentiation to an integral power \>= 1
expt1 (*~) x n
    | n == 1    = x
    | odd n     = x *~ expt1 (*~) x (n - 1)
    | otherwise = assert (n > 1) $ expt1 (*~) (x *~ x) (n `quot` 2)
{-# SPECIALIZE expt1 :: Op2 a -> a -> Int -> a #-}

gpExpt          :: Integral b => Group a -> a -> b -> a
-- ^ exponentiation to an integral power
gpExpt (MkMonoid { .. }) x n
    | n > 0     = expt1 op x n
    | n == 0    = ident
    | otherwise = inv (expt1 op x (- n))
{-# SPECIALIZE gpExpt :: Group a -> a -> Int -> a #-}

pairMon         :: MonoidOps a -> MonoidOps b -> MonoidOps (a :!: b)
-- ^ Direct product of two monoids. If both are 'Group's, then the result is also.
pairMon aM bM   =
    MkMonoid (MonoidFlags { .. })
        (liftEq2 aM.eq bM.eq)
        (pairOp2 aM.op bM.op)
        (aM.ident :!: bM.ident)
        (\ (a :!: ~b) -> aM.isIdent a && bM.isIdent b)
        (bimap aM.inv bM.inv)
  where
    aFlags      = aM.monFlags
    bFlags      = bM.monFlags
    nontrivial  = aFlags.nontrivial || bFlags.nontrivial
    abelian     = aFlags.abelian && bFlags.abelian
    isGroup     = aFlags.isGroup && bFlags.isGroup

gpModF          :: Group g -> Op1 g -> MonoidFlags -> Group (Cls g)
-- ^ @gpModF gp reduce@ is @gp@ modulo a normal subgroup, using @reduce@ to produce @Cls@
-- (coset) representatives.
gpModF (MkMonoid { .. }) reduce extraFlags  =
    let modF    = Cls . reduce
        redId   = reduce ident
        flags   = MonoidFlags { nontrivial = False, abelian = monFlags.abelian,
                    isGroup = monFlags.isGroup }
    in  MkMonoid (flags <> extraFlags)
            (eq `on` (.rep)) (modF .* (op `on` (.rep))) (Cls redId)
            ((if isIdent redId then isIdent else eq redId) . (.rep))
            (modF . inv . (.rep))

monProductL'    :: Foldable f => MonoidOps g -> f g -> g
-- ^ product using foldl'
monProductL' gM = foldl' gM.op gM.ident

monProductR     :: Foldable f => MonoidOps g -> f g -> g
-- ^ product using foldr
monProductR gM  = foldr gM.op gM.ident

-- ** AbelianGroup

type AbelianGroup       = Group
{- ^ 'abelian' must be @True@. We then usually use additive notation, as in the next few
    functions. -}

pattern AbelianGroup    :: MonoidFlags -> EqRel a -> Op2 a -> a -> Pred a -> Op1 a ->
                            AbelianGroup a
pattern AbelianGroup { monFlags, eq, plus, zero, isZero, neg }  =
    MkMonoid { monFlags, eq, op = plus, ident = zero, isIdent = isZero, inv = neg }
{-# COMPLETE AbelianGroup #-}

instance HasField "plus" (AbelianGroup g) (Op2 g) where
    getField (AbelianGroup { plus }) = plus
instance HasField "zero" (AbelianGroup g) g where
    getField (AbelianGroup { zero }) = zero
instance HasField "isZero" (AbelianGroup g) (Pred g) where
    getField (AbelianGroup { isZero }) = isZero
instance HasField "neg" (AbelianGroup g) (Op1 g) where
    getField (AbelianGroup { neg }) = neg

minus           :: AbelianGroup a -> Op2 a
-- ^ @minus ag x y = x \`plus\` neg y@
minus (AbelianGroup { .. }) x y  = x `plus` neg y

sumL'           :: Foldable f => AbelianGroup a -> f a -> a
-- ^ sum using foldl'
sumL'           = monProductL'

sumR            :: Foldable f => AbelianGroup a -> f a -> a
-- ^ sum using foldr
sumR            = monProductR


-- * Rings and fields

{- $rings
    A /ring/ is an abelian group, together with an associative multiplication with identity.
    Multiplication must distribute over addition. -}

-- ** RingFlags

data RingFlags  = RingFlags {
        commutative     :: Bool,    -- ^ \=> multiplication is commutative
        noZeroDivisors  :: Bool,    -- ^ \=> (ab == 0 => a == 0 or b == 0)
        nzInverses      :: Bool     -- ^ \=> every nonzero element has a multiplicative inverse,
            -- which 'rInv' finds; this implies 'noZeroDivisors'
    } deriving (Eq, Show)
-- ^ known properties of a t'Ring'

instance Semigroup RingFlags where
    x <> y      = RingFlags {
            commutative     = x.commutative    || y.commutative,
            noZeroDivisors  = x.noZeroDivisors || y.noZeroDivisors,
            nzInverses      = x.nzInverses || y.nzInverses
        }
-- ^ @(\<>)@ is @(||)@ applied to each property

integralDomainFlags :: RingFlags
{- ^ An /integral domain/ is a commutative ring with 0 \/= 1 and no zero divisors. It must
    contain the flags @'nontrivial' = True@ and 'integralDomainFlags'. -}
integralDomainFlags =
    RingFlags { commutative = True, noZeroDivisors = True, nzInverses = False }

divisionRingFlags   :: RingFlags
{- ^ A /division ring/ is a ring with 0 \/= 1 and every nonzero element has a (computable)
    multiplicative inverse. It must contain the flags @'nontrivial' = True@ and
    'divisionRingFlags'. -}
divisionRingFlags   =
    RingFlags { commutative = False, noZeroDivisors = True, nzInverses = True }

fieldFlags          :: RingFlags
{- ^ A 'Field' is a commutative division ring. It must contain the flags @'nontrivial' = True@
    and 'fieldFlags'. -}
fieldFlags          = integralDomainFlags <> divisionRingFlags

-- ** Ring

newtype IsDeep      = IsDeep { b :: Bool }  deriving Show
-- ^ whether to go beyond a \"top\" level

{- | A t'Ring' must satisfy the axioms below. Examples include the integers ℤ, and other rings
    of algebraic numbers, polynomials, n x n matrices, etc. -}
data Ring a         = Ring {
    ag      :: AbelianGroup a,
    rFlags  :: RingFlags,
    times   :: Op2 a,       -- ^ @(*.)@ is well defined, distributes over @plus@, and is
        -- normally associative
    one     :: a,           -- ^ @(one *.) = (*. one) = id@
    fromZ   :: Integer -> a,    -- ^ the unique ring homomorphism from Z to this ring
    bDiv    :: IsDeep -> a -> a -> (a, a)    {- ^ @bDiv doFull y m = (q, r) => y = m*q + r@ and
        @r@'s \"size\" is (attempted to be) minimized. If @doFull.b@, then all of @r@ is
        minimized; else just its \"topmost\" nonzero \"term\" is. (Words such as \"size\" have
        meanings that vary by context. Also in general, the results of @bDiv@ may not be
        uniquely determined by these requirements. Finally, note that @m@ is allowed to be 0.)
        -}
}
-- ^ A ring is /commutative/ if @*.@ is. A /unit/ is an element @x@ such that there exists a
-- @y@ with @x *. y = y *. x = one@.
--
-- A /homomorphism of rings/ @f :: R -> R'@ is an additive (Abelian group) homomorphism that
-- also satisfies @f (x *. y) = f x *. f y@ and @f one = one'@.

instance HasField "eq" (Ring r) (r -> r -> Bool) where
    getField rR = rR.ag.eq
instance HasField "plus" (Ring r) (Op2 r) where
    getField rR = rR.ag.plus
instance HasField "zero" (Ring r) r where
    getField rR = rR.ag.zero
instance HasField "isZero" (Ring r) (Pred r) where
    getField rR = rR.ag.isZero
instance HasField "neg" (Ring r) (Op1 r) where
    getField rR = rR.ag.neg

rIsOne          :: Ring a -> Pred a
-- ^ > rIsOne aR = aR.eq aR.one
rIsOne aR       = aR.eq aR.one

exactQuo        :: Ring a -> Op2 a
-- ^ exact quotient, i.e. division (@bDiv (IsDeep False)@) should have zero remainder
exactQuo rR y m =
    let (q, r)      = rR.bDiv (IsDeep False) y m
    in  if rR.isZero r then q else error "division is not exact"

nearQuo                 :: Ring a -> IsDeep -> Op2 a
-- ^ > nearQuo rR doFull y m = fst (rR.bDiv doFull y m)
nearQuo rR doFull y m   = fst (rR.bDiv doFull y m)
smallRem                :: Ring a -> IsDeep -> Op2 a
-- ^ > smallRem rR doFull y m = snd (rR.bDiv doFull y m)
smallRem rR doFull y m  = snd (rR.bDiv doFull y m)

rInv            :: Ring a -> Op1 a
-- ^ > rInv rR = exactQuo rR rR.one
rInv rR         = exactQuo rR rR.one

divides         :: Ring a -> a -> a -> Bool
-- ^ whether an element divides another element; note the arguments are reversed from division
divides rR d y  = rR.isZero (snd (rR.bDiv (IsDeep False) y d))

rExpt           :: Integral b => Ring a -> a -> b -> a
-- ^ exponentiation to an integral power
rExpt rR x n
    | n > 0     = expt1 rR.times x n
    | n == 0    = rR.one
    | otherwise = rInv rR (rExpt rR x (- n))
{-# SPECIALIZE rExpt :: Ring a -> a -> Int -> a #-}

rSumL'          :: Foldable f => Ring a -> f a -> a
-- ^ sum using foldl'
rSumL' aR       = sumL' aR.ag

rSumR           :: Foldable f => Ring a -> f a -> a
-- ^ sum using foldr
rSumR aR        = sumR aR.ag

rProductL'      :: Foldable f => Ring g -> f g -> g
-- ^ product using foldl'
rProductL' Ring{ .. }   = foldl' times one

rProductR       :: Foldable f => Ring g -> f g -> g
-- ^ product using foldr
rProductR Ring{ .. }    = foldr times one

-- ** Field

type Field      = Ring
{- ^ A 'Field' is a commutative division ring. It must contain the flags @'nontrivial' = True@
    and 'fieldFlags'. -}

divisionRing    :: AbelianGroup a -> RingFlags -> Op2 a -> a -> (Integer -> a) -> Op1 a ->
                    Ring a
-- ^ @(divisionRing ag extraFlags (*~) one fromZ inv)@ creates a division ring
divisionRing ag extraFlags (*~) one fromZ inv   =
    let bDiv _ y m  = if ag.isZero m then (ag.zero, y) else (inv m *~ y, ag.zero)
    in  Ring ag (divisionRingFlags <> extraFlags) (*~) one fromZ bDiv

field           :: AbelianGroup a -> Op2 a -> a -> (Integer -> a) -> Op1 a -> Field a
-- ^ @field ag (*~) one fromZ inv@ creates a 'Field'
field ag        = divisionRing ag fieldFlags

fieldGcd        :: Field a -> Op2 a
-- ^ creates a gcd (greatest common divisior) function for a 'Field'
fieldGcd (Ring ag _ _ one _ _) x y  = if ag.isZero x && ag.isZero y then ag.zero else one


-- * Modules and R-algebras

-- ** Module, RMod, ModR

{- | Given an Abelian group G, End(G) = { endomorphisms of G } = { homomorphisms G -> G } is
    a ring, with @*.@ given by composition. Given a ring R, a /left module over R/ is an
    Abelian group M together with a ring homomorphism R -> End(M). A /right module over R/
    has the same definition, but with function composition defined on the right, i.e. by
    @(flip .)@. A /module/ is either a left module or a right module. -}
data Module r m     = Module {
    ag          :: AbelianGroup m,
    scale       :: r -> Op1 m,
    bDiv        :: IsDeep -> m -> m -> (r, m)
        -- ^ like @bDiv@ for a t'Ring' (as a right module over itself),
        -- @bDiv doFull y m = (q, r) => y = scale q m + r@,
}
{- ^ A /vector space/ is a module over a field.

    A /homomorphism of R-modules/ or /R-linear map/ @f :: M -> M'@ is an additive homomorphism
    that also satisfies @f (r \`scale\` m) = r \`scale\` f m@. -}

newtype IsLeftMod   = IsLeftMod { b :: Bool }   deriving (Eq, Show)
-- ^ whether a t'Module' is a left module

type RMod           = Module
-- ^ a left module over R
type ModR           = Module
-- ^ a right module over R

pairMd              :: Ring r -> Module r a -> Module r b -> Module r (a :!: b)
-- ^ direct sum (or product) of two left modules or two right modules
pairMd rR aMd bMd   =
    Module (pairMon aMd.ag bMd.ag) (\r -> bimap (aMd.scale r) (bMd.scale r)) pairBDiv
  where
    pairBDiv doFull (y :!: z) (m :!: n)
        | aMd.ag.isZero m && doFull.b   =
            let (q, r) = bMd.bDiv doFull z n
            in  (q, y :!: r)
        | otherwise                     =
            let (q, r)  = aMd.bDiv doFull y m
            in  (q, r :!: bMd.ag.plus z (bMd.scale (rR.neg q) n))

mdModF              :: Module r a -> Op1 a -> MonoidFlags -> Module r (Cls a)
{- ^ @(mdModF md reduce extraFlags)@ is @md@ modulo a submodule, using @reduce@ to produce @Cls@
    (coset) representatives. This @bDiv@ is very naive. -}
mdModF (Module { .. }) reduce extraFlags    =
    Module (gpModF ag reduce extraFlags) (\ r (Cls m) -> modF (scale r m)) modBDiv
  where
    modF    = Cls . reduce
    modBDiv doFull (Cls m) (Cls n)  = second modF (bDiv doFull m n)

-- ** RAlg

{- | Given a commutative ring @R@, an /R-algebra/ is a ring @A@ together with a ring
    homomorphism @R -> center(A)@. (The /center/ of a group or ring is the set of elements that
    commute with every element of the group or ring.) This makes @A@ into an @R-module@. -}
data RAlg r a       = RAlg {
    aR          :: Ring a,
    scale       :: r -> Op1 a,
    fromR       :: r -> a
}

algMd           :: RAlg r a -> (IsDeep -> a -> a -> (r, a)) -> Module r a
-- ^ > algMd (RAlg { .. }) bDiv = Module aR.ag scale bDiv
algMd (RAlg { .. })     = Module aR.ag scale


-- * Basic numeric rings

numAG           :: forall n. (Eq n, Num n) => AbelianGroup n
-- ^ @(n)@ under addition
numAG           = AbelianGroup (agFlags nontriv) (==) (+) 0 (== 0) negate
  where
    nontriv         = IsNontrivial ((0 :: n) /= 1)

numRing         :: (Eq n, Num n) => RingFlags -> (IsDeep -> n -> n -> (n, n)) -> Ring n
-- ^ @(n)@ as a t'Ring'; @(numRing rFlags bDiv)@
numRing rFlags  = Ring numAG rFlags (*) 1 fromInteger

-- ** Integer

zzAG            :: AbelianGroup Integer
-- ^ the integers ℤ under addition
zzAG            = numAG

zzDiv           :: IsDeep -> Integer -> Integer -> (Integer, Integer)
-- ^ integer division, including by 0, minimizing the absolute value of the remainder
zzDiv _ n d
    | d == 0    = (0, n)
    | d < 0     = let (q, r) = zzDiv (IsDeep False) n (- d) in (- q, r)
    | otherwise = let (q, r) = divMod n d
                  in  if 2*r < d then (q, r) else (q + 1, r - d)

zzRing          :: Ring Integer
-- ^ the ring of integers ℤ
zzRing          = numRing integralDomainFlags zzDiv

-- ** Double

dblAG           :: AbelianGroup Double
-- ^ Double precision numbers under addition
dblAG           = numAG

dblRing         :: Field Double
-- ^ the approximate field of Doubles
dblRing         = field dblAG (*) 1 fromInteger recip


-- * Converting -> Text

show0x          :: (Integral a, Show a) => a -> String
-- ^ show in hexadecimal with a "0x" prefix; the argument must be nonnegative
show0x n        = "0x" <> showHex n ""

showT           :: Show a => a -> Text
-- ^ Convert a value to 'Text' using a 'Show' instance.
showT           = T.pack . show

-- ** With Precedence

{- | Precedence of a prefix, infix, or postfix operator. Numeric values may differ from
    Haskell's built-in ones, and new ones may be added in the future. -}
data Prec       =
          CommaPrec
        | AddPrec       -- ^ addition or subtraction, left associative
        | MultPrec      -- ^ multiplication or division, left associative
        | ExptPrec      -- ^ exponentiation or negation (prefix @\"-\"@), right associative
        | AtomPrec      {- ^ an atomic expression, such as an unsigned number, atomic variable,
                            or atomic constant -}
        | FencePrec     {- ^ a parenthesized or otherwise \"fenced\" expression; note higher
                            than 'AtomPrec' -}
    deriving (Eq, Ord, Enum, Bounded, Show)

data PrecText   = PrecText { prec :: Prec, t :: Text }
    deriving (Eq, Show)     -- e.g. for testing & debugging
-- ^ A mathematical expression, and the precedence of its outermost operator.

instance Buildable PrecText where
    build       = build . (.t)
-- ^ discards the precedence

parensIf        :: Bool -> Text -> Text
-- ^ @parensIf b t@ encloses @t@ in parentheses if @b@
parensIf b t    = if b then T.concat ["(", t, ")"] else t

ensurePrec      :: Prec -> PrecText -> Text
-- ^ parenthesize an expression if its precedence is below the given value
ensurePrec minP pt  = parensIf (pt.prec < minP) pt.t

infixGenPT      :: Op1 Prec -> Op1 Prec -> Prec -> Text -> Op2 PrecText
{- ^ format using an infix operator that requires the given left and right precedence increments
    arounds its operands -}
infixGenPT dl dr prec op x y    =
    PrecText prec (T.concat [ensurePrec (dl prec) x, op, ensurePrec (dr prec) y])

infixLPT        :: Prec -> Text -> Op2 PrecText
-- ^ format using a non-associative @infixl@ operator
infixLPT        = infixGenPT id succ

infixRPT        :: Prec -> Text -> Op2 PrecText
-- ^ format using a non-associative @infixr@ operator
infixRPT        = infixGenPT succ id

infixAssocPT    :: Prec -> Text -> Op2 PrecText
{- ^ format using an infix operator that doesn't require parentheses around operands of the same
    precedence -}
infixAssocPT    = infixGenPT id id

infixPT         :: Prec -> Text -> Op2 PrecText
{- ^ format using an infix operator that requires parentheses around operands of the same
    precedence -}
infixPT         = infixGenPT succ succ

infixListPT     :: Foldable f => Prec -> Bool -> Text -> f PrecText -> PrecText
{- ^ @(infixListPT opPrec parenTies op args)@ combines the @args@ using the infix operator @op@.
    @parenTies@ says whether to parenthesize arguments whose precedence is exactly @opPrec@. -}
infixListPT opPrec parenTies op (toList -> args)
    | null args         = PrecText minBound ""
    | [arg] <- args     = arg
    | let minP = (if parenTies then succ else id) opPrec
                        = PrecText opPrec (T.intercalate op (map (ensurePrec minP) args))

fencePT         :: Text -> Text -> Text -> PrecText
{-^ @(fencePT open inner close)@ creates a \"fenced\" (parenthesized, bracketed, etc.)
    expression around @inner@. -}
fencePT open inner close    = PrecText FencePrec (T.concat [open, inner, close])

sumPT           :: Foldable f => f PrecText -> PrecText
-- ^ Sum of expressions, checking args for 0 and prefix @\"-\"@.
sumPT           = go . filter (\pt -> pt.t /= "0") . toList
  where
    go []           = PrecText AtomPrec "0"
    go [pt]         = pt
    go pts          = PrecText AddPrec (dropPlus (T.concat (map toSignedArg pts)))
    dropPlus t      = fromMaybe t (T.stripPrefix "+" t)
    toSignedArg     = addPlus . ensurePrec AddPrec
    addPlus t       = if T.isPrefixOf "-" t then t else "+" <> t

plusPT          :: Op2 PrecText
-- ^ Sum of two expressions, checking args for 0 and prefix @\"-\"@.
plusPT aPT bPT  = sumPT [aPT, bPT]

timesPT         :: Op2 PrecText
-- ^ Product of two expressions, checking args for 1, prefix @\"-\"@, and concatenating digits.
timesPT aPT bPT
    | aPT.t == "1"      = bPT
    | bPT.t == "1"      = aPT
    | aPT.t == "-1"     =
        PrecText (if bPT.prec < MultPrec then ExptPrec else min bPT.prec ExptPrec) ("-" <> bT)
    | otherwise         = PrecText MultPrec (ensurePrec MultPrec aPT <> b1T)
  where
    ~bT             = ensurePrec MultPrec bPT
    ~b1T            = parensIf (needsLParen bT) bT
    needsLParen     = maybe False (\(c, _) -> c == '-' || isDigit c) . T.uncons

productPT       :: Foldable f => f PrecText -> PrecText
-- ^ Product of expressions, checking args for 1, prefix @\"-\"@, and concatenating digits.
productPT       = foldl' timesPT (PrecText AtomPrec "1")

exptPT          :: Op2 PrecText
-- ^ @\"^\"@ of two expressions
exptPT          = infixRPT ExptPrec "^"

type ShowPrec a = a -> PrecText
-- ^ convert to a mathematical expression and its outermost precedence

integralPT      :: (Integral a, Show a) => ShowPrec a
-- ^ show an 'Int'/'Integer'/etc. with precedence
integralPT n    = PrecText (if n < 0 then ExptPrec else AtomPrec) (showT n)

zzShowPrec      :: ShowPrec Integer
-- ^ show an 'Integer' with precedence
zzShowPrec      = integralPT

hex0xPT         :: (Integral a, Show a) => ShowPrec a
-- ^ show in hexadecimal with a "0x" prefix; the argument must be nonnegative
hex0xPT n       = assert (n >= 0) $ PrecText AtomPrec (T.pack (show0x n))

integralPowPT   :: (Integral d, Show d) => PrecText -> ShowPrec d
-- ^ Power of a given base, checking the exponent for 0 or 1.
integralPowPT bPT d     = case d of
    0   -> PrecText AtomPrec "1"
    1   -> bPT
    _   -> exptPT bPT (integralPT d)

sPairShowPrec   :: ShowPrec a -> ShowPrec b -> ShowPrec (a :!: b)
-- ^ show a strict pair with precedence
sPairShowPrec aSP bSP (a :!: b)     = PrecText FencePrec (T.concat ["(", aT, ", ", bT, ")"])
  where
    aT      = ensurePrec (succ CommaPrec) (aSP a)
    bT      = ensurePrec (succ CommaPrec) (bSP b)

infixCommasPT   :: Foldable f => Text -> f PrecText -> Text -> PrecText
-- ^ show a 'Foldable' as a fenced list separated by commas, with precedence
infixCommasPT open args     = fencePT open (infixListPT CommaPrec True ", " args).t

listShowPrec    :: (Functor f, Foldable f) => ShowPrec e -> ShowPrec (f e)
-- ^ show a 'Foldable' as a list, with precedence
listShowPrec eSP es     = infixCommasPT "[" (fmap eSP es) "]"

gensShowPrec    :: (Functor f, Foldable f) => ShowPrec g -> f g -> PrecText
-- ^ show a list of generators, with precedence
gensShowPrec gSP gs     = infixCommasPT "⟨" (fmap gSP gs) "⟩"


-- * Parsing

type Parser     = Parsec Void Text
{- ^ A monad for parsing, using the [megaparsec](https://hackage.haskell.org/package/megaparsec)
    and [parser-combinators](https://hackage.haskell.org/package/parser-combinators) libraries.
    Unless otherwise specified, parsers consume any following white space and comments, but not
    leading ones. -}

spaceConsumer   :: Parser ()
{- ^ Consumes (skips) any white space, @\/\/@ end-of-line comments, and @\/\* ... *\/@ nestable
    block comments. -}
spaceConsumer   = L.space space1 (L.skipLineComment "//") (L.skipBlockCommentNested "/*" "*/")

parseAllOrErr   :: Parser a -> Text -> a
-- ^ Parse an entire input, or call 'error' on failure.
parseAllOrErr p t   = either (error . errorBundlePretty) id (parse pAll "" t)
  where
    pAll    = spaceConsumer >> p <* eof

pLexeme         :: Op1 (Parser a)
{- Uses the given lexeme parser, followed by 'spaceConsumer' to skip any following white space
    and comments. -}
pLexeme         = L.lexeme spaceConsumer

pSymbol         :: Text -> Parser Text
-- Parses the verbatim text, followed by any white space and comments.
pSymbol         = L.symbol spaceConsumer

pInfixL         :: Parser a -> Parser (a -> b -> a) -> Parser b -> Parser a
-- ^ Parse left-associative operator(s) with the same precedence.
pInfixL pA pOp pB   = pA >>= pOpBs
  where
    pOpBs a     = do
            op      <- pOp
            b       <- pB
            pOpBs (a `op` b)
        <|> pure a

pParens         :: Parser a -> Parser a
-- ^ Parse an expression in parentheses.
pParens         = between (pSymbol "(") (pSymbol ")")

zzParse         :: Parser Integer
-- ^ Parse an optional sign, followed by a decimal integer.
zzParse         = L.signed spaceConsumer (pLexeme L.decimal)

agParse         :: AbelianGroup g -> Parser g -> Parser g
{- ^ Parse a sum of terms or @\"-\"@ terms, given a parser for a single term. -}
agParse ag pTerm    = sumR ag <$> liftA2 (:) (pOpTerm <|> pTerm) (many pOpTerm)
    -- make right-associative for efficiency in common cases
  where
    pOpTerm     = (pSymbol "+" *> pTerm)
              <|> (pSymbol "-" *> (ag.neg <$> pTerm))

rngParse        :: Ring r -> Parser r -> Parser r
{- ^ Parse a ring element as a sum of products or quotients of integer powers of \"atom\"s,
    given an \"atom\" parser. -}
rngParse rR@(Ring { .. }) pAtom     = pR
  where
    pPower  = liftA2 (rExpt rR) (pAtom <|> pParens pR) (pSymbol "^" *> zzParse <|> pure 1)
    pOp     = pSymbol "/" $> exactQuo rR
         <|> (pSymbol "*" <|> notFollowedBy digitChar $> "") $> times
    pR      = agParse ag (pInfixL pPower pOp pPower)

zzGensRingParse     :: Ring r -> Parser r -> Parser r
{- ^ Parse a ring element, given a parser for \"generators\". Each generator name should not
    start with white space or a ring operator. -}
zzGensRingParse rR pGen     = rngParse rR pAtom
  where
    pAtom       = pGen <|> rR.fromZ <$> pLexeme L.decimal
                    <?> "expression"


-- * Variable names

numVarPT        :: Text -> Int -> PrecText
{- ^ Create a variable name from a prefix, usually a single unicode letter, followed by a
    number, which is usually nonnegative. -}
numVarPT prefix n   = PrecText AtomPrec (prefix <> showT n)

alphaNumVarNames    :: [Text]
-- ^ An infinite list of variable names: @a-z, A-Z, xN@ for @N > 0@.
alphaNumVarNames    = (T.singleton <$> ['a' .. 'z'] ++ ['A' .. 'Z'])
                        ++ (T.cons 'x' . showT <$> [1 :: Int ..])

varNameParse    :: Parser Text
-- ^ Parse a mathematical variable name: a unicode letter, optionally followed by digits.
varNameParse    = T.pack <$> liftA2 (:) letterChar (many digitChar)

varParse        :: [Text] -> [a] -> Parser a
-- ^ Parse a mathematical variable name, using lists of names and values.
varParse names vals     = do
    name        <- varNameParse
    pure $ fromMaybe (error ("Name not found: "+|name|+"")) (lookup name (zip names vals))
