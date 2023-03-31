{-# LANGUAGE Strict #-}

{- |  This module defines the most common types of algebras, and simple functions using them.
    
    An /algebraic structure/ or /algebra/ is a set together with a collection of operations
    (functions) on it that satisfy some specified axioms (identities). Algebras are important
    computationally because working over them allows us to implement an algorithm once, in its
    natural level of generality. We often want to construct or analyze specific algebras, often
    by using other algebras. We implement an algebra using a first-class data value rather than
    a type class, because a single type may admit more than one structure as a given type of
    algebra. (For example, consider quotient algebras such as @ℤ/pℤ@ or @R[X, Y]/(f, g)@ for
    various @p@, @f@, and @g@.) Also, treating algebras as first-class values allows us to
    construct them at arbitrary times in arbitrary ways.
    
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
    Cmp,
    cmpEq,
    maxBy, minBy,
    lex2Cmp, liftCompare,
    
    -- * Groups
    -- ** MonoidFlags
    show0x, IntBits, (.&.), (.|.), zeroBits, eiBit, eiBits, hasEIBit, hasEIBits,
    MonoidFlag(Abelian, IsGroup), MonoidFlags, agFlags,
    -- ** Group
    Group(..), expt1, gpExpt, pairGp, gpModF, gpProductL', gpProductR,
    -- ** AbelianGroup
    AbelianGroup(), pattern AbelianGroup,   -- @@@ fails: plus, zero, isZero, neg,
    agPlus, agZero, agIsZero, agNeg, abelianGroup,
    minus, sumL', sumR,
    
    -- * Rings and fields
    -- ** RingFlags
    RingFlag(NotZeroRing, IsCommutativeRing, NoZeroDivisors, IsInversesRing), RingFlags,
    integralDomainFlags, divisionRingFlags, fieldFlags,
    -- ** Ring
    Ring(..), rEq, rPlus, rZero, rIsZero, rNeg,
    rIsOne, exactQuo, nearQuo, smallRem, rInv, divides,
    rExpt, rSumL', rSumR, rProductL', rProductR,
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
    zzAG, zzDiv, zzRing,
    -- ** Double
    dblAG, dblRing,
    
    -- * Converting \<-> String
    pairShows, showGens,
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

newtype Cls a   = Cls { rep :: a }  deriving (Eq, Show)
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
data Group g        = Group {
    monFlags    :: MonoidFlags,
    eq          :: EqRel g,     -- ^ @eq x y@ must imply abstract equality @x = y@
    op          :: Op2 g,       -- ^ @op@ is well defined and associative
    ident       :: g,           -- ^ @(ident \`op\`) = (\`op\` ident) = id@
    isIdent     :: Pred g,      -- ^ @isIdent x = ident \`eq\` x@ for all @x@
    inv         :: Op1 g        -- ^ @(inv x) \`op\` x = x \`op\` (inv x) = ident@ for all @x@;
        -- therefore @inv@ is well defined also
}
{- ^ A /homomorphism of groups/ is a well defined function @f :: G -> G'@ that satisfies
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
gpExpt (Group { .. }) x n
    | n > 0     = expt1 op x n
    | n == 0    = ident
    | otherwise = inv (expt1 op x (- n))
{-# SPECIALIZE gpExpt :: Group a -> a -> Int -> a #-}

pairGp          :: Group a -> Group b -> Group (a, b)
-- ^ direct product of two groups
pairGp aGp bGp  =
    Group (aGp.monFlags .&. bGp.monFlags)
          (pairEq aGp.eq bGp.eq)
          (pairOp2 aGp.op bGp.op)
          (aGp.ident, bGp.ident)
          (\ (a, ~b) -> aGp.isIdent a && bGp.isIdent b)
          (pairOp1 aGp.inv bGp.inv)

gpModF          :: Group g -> Op1 g -> MonoidFlags -> Group (Cls g)
-- ^ @gpModF gp reduce@ is @gp@ modulo a normal subgroup, using @reduce@ to produce @Cls@
-- (coset) representatives.
gpModF (Group { .. }) reduce extraFlags     =
    let modF    = Cls . reduce
        redId   = reduce ident
    in  Group (monFlags .|. extraFlags)
            (eq `on` (.rep)) (modF .* (op `on` (.rep))) (Cls redId)
            ((if isIdent redId then isIdent else eq redId) . (.rep))
            (modF . inv . (.rep))

gpProductL'     :: Group g -> [g] -> g
-- ^ product using foldl'
gpProductL' Group{ .. }     = foldl' op ident

gpProductR      :: Group g -> [g] -> g
-- ^ product using foldr
gpProductR Group{ .. }      = foldr op ident

-- ** AbelianGroup

type AbelianGroup       = Group
{- ^ @op@ must be commutative. We then usually use additive notation, as in the next few
    functions. -}
pattern AbelianGroup    :: MonoidFlags -> EqRel a -> Op2 a -> a -> Pred a -> Op1 a -> Group a
pattern AbelianGroup { monFlags, eq, plus, zero, isZero, neg }  =
    Group { monFlags, eq, op = plus, ident = zero, isIdent = isZero, inv = neg }
{-# COMPLETE AbelianGroup #-}

agPlus          :: AbelianGroup a -> Op2 a
-- ^ @agPlus = (.op)@
agPlus (AbelianGroup { .. })    = plus
agZero          :: AbelianGroup a -> a
-- ^ @agZero = (.ident)@
agZero          = (.ident)
agIsZero        :: AbelianGroup a -> Pred a
-- ^ @agIsZero = (.isIdent)@
agIsZero        = (.isIdent)
agNeg           :: AbelianGroup a -> Op1 a
-- ^ @agNeg = (.inv)@
agNeg           = (.inv)

abelianGroup    :: EqRel a -> Op2 a -> a -> Pred a -> Op1 a -> AbelianGroup a
-- ^ @abelianGroup eq plus zero isZero neg@ creates an 'AbelianGroup'
abelianGroup    = AbelianGroup agFlags

minus           :: AbelianGroup a -> Op2 a
-- ^ @minus ag x y = x `plus` neg y@
minus (AbelianGroup { .. }) x y  = x `plus` neg y

sumL'           :: AbelianGroup a -> [a] -> a
-- ^ sum using foldl'
sumL'           = gpProductL'

sumR            :: AbelianGroup a -> [a] -> a
-- ^ sum using foldr
sumR            = gpProductR


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

{- | A @(Ring ag (*~) one fromZ bDiv)@ must satisfy the axioms below. Examples include the
    integers ℤ, and other rings of algebraic numbers, polynomials, n x n matrices, etc. -}
data Ring a         = Ring {
    ag          :: AbelianGroup a,
    rFlags      :: RingFlags,
    times       :: Op2 a,       -- ^ @(*.)@ is well defined, distributes over @plus@, and is
        -- normally associative
    one     :: a,           -- ^ @(one *.) = (*. one) = id@
    fromZ   :: Integer -> a,    -- ^ the unique ring homomorphism from Z to this ring
    bDiv    :: Bool -> a -> a -> (a, a)     {- ^ @bDiv doFull y m = (q, r) => y = m*q + r@ and
        @r@'s \"size\" is (attempted to be) minimized. If @doFull@, then all of @r@ is
        minimized; else just its \"topmost\" nonzero \"term\" is. (Words such as \"size\" have
        meanings that vary by context. Also in general, the results of @bDiv@ may not be
        uniquely determined by these requirements.) -}
}
-- ^ A ring is /commutative/ if @*.@ is. A /unit/ is an element @x@ such that there exists a
-- @y@ with @x *. y = y *. x = one@.
--
-- A /homomorphism of rings/ @f :: R -> R'@ is an additive (Abelian group) homomorphism that
-- also satisfies @f (x *. y) = f x *. f y@ and @f one = one'@.

rEq             :: Ring a -> EqRel a
-- ^ > rEq = (.eq) . (.ag)
rEq aR          = aR.ag.eq
rPlus           :: Ring a -> Op2 a
-- ^ > rPlus = agPlus . (.ag)
rPlus           = agPlus . (.ag)
rZero           :: Ring a -> a
-- ^ > rZero = agZero . (.ag)
rZero           = agZero . (.ag)
rIsZero         :: Ring a -> Pred a
-- ^ > rIsZero = agIsZero . (.ag)
rIsZero         = agIsZero . (.ag)
rNeg            :: Ring a -> Op1 a
-- ^ > rNeg = agNeg . (.ag)
rNeg            = agNeg . (.ag)

rIsOne          :: Ring a -> Pred a
-- ^ > rIsOne aR = rEq aR aR.one
rIsOne aR       = rEq aR aR.one

exactQuo        :: Ring a -> Op2 a
-- ^ exact quotient, i.e. division (@bDiv False@) should have zero remainder
exactQuo rR y m =
    let (q, r)      = rR.bDiv False y m
    in  if rIsZero rR r then q else error "division is not exact"

nearQuo                 :: Ring a -> Bool -> Op2 a
-- ^ > nearQuo rR doFull y m = fst (rR.bDiv doFull y m)
nearQuo rR doFull y m   = fst (rR.bDiv doFull y m)
smallRem                :: Ring a -> Bool -> Op2 a
-- ^ > smallRem rR doFull y m = snd (rR.bDiv doFull y m)
smallRem rR doFull y m  = snd (rR.bDiv doFull y m)

rInv            :: Ring a -> Op1 a
-- ^ > rInv rR = exactQuo rR rR.one
rInv rR         = exactQuo rR rR.one

divides         :: Ring a -> a -> a -> Bool
-- ^ whether an element divides another element; note the arguments are reversed from division
divides rR d y  = rIsZero rR (snd (rR.bDiv False y d))

rExpt           :: Integral b => Ring a -> a -> b -> a
-- ^ exponentiation to an integral power
rExpt rR x n
    | n > 0     = expt1 rR.times x n
    | n == 0    = rR.one
    | otherwise = rInv rR (rExpt rR x (- n))
{-# SPECIALIZE rExpt :: Ring a -> a -> Int -> a #-}

rSumL'          :: Ring a -> [a] -> a
-- ^ sum using foldl'
rSumL' aR       = sumL' aR.ag

rSumR           :: Ring a -> [a] -> a
-- ^ sum using foldr
rSumR aR        = sumR aR.ag

rProductL'      :: Ring g -> [g] -> g
-- ^ product using foldl'
rProductL' Ring{ .. }   = foldl' times one

rProductR       :: Ring g -> [g] -> g
-- ^ product using foldr
rProductR Ring{ .. }    = foldr times one

-- ** Field

type Field      = Ring
{- ^ A /division ring/ is a ring with @zero \/= one@ and in which every non-zero element is a
    unit. A /field/ is a commutative division ring. -}

divisionRing    :: AbelianGroup a -> RingFlags -> Op2 a -> a -> (Integer -> a) -> Op1 a ->
                    Ring a
-- ^ @divisionRing ag extraFlags (*~) one fromZ inv@ creates a division ring
divisionRing ag extraFlags (*~) one fromZ inv   =
    let zero        = agZero ag
        bDiv _ y m      = if agIsZero ag m then (zero, y) else (inv m *~ y, zero)
    in  Ring ag (divisionRingFlags .|. extraFlags) (*~) one fromZ bDiv

field           :: AbelianGroup a -> Op2 a -> a -> (Integer -> a) -> Op1 a -> Field a
-- ^ @field ag (*~) one fromZ inv@ creates a 'Field'
field ag        = divisionRing ag fieldFlags

fieldGcd        :: Field a -> Op2 a
-- ^ creates a gcd (greatest common divisior) function for a 'Field'
fieldGcd (Ring ag _ _ one _ _) x y  = if agIsZero ag x && agIsZero ag y then agZero ag else one


-- * Modules and R-algebras

-- ** Module, RMod, ModR

{- | Given an Abelian group G, End(G) = { endomorphisms of G } = { homomorphisms G -> G } is
    a ring, with @*.@ given by composition. Given a ring R, a /left module over R/ is an
    Abelian group M together with a ring homomorphism R -> End(M). A /right module over R/
    has the same definition, but with function composition defined on the right, i.e. by
    @(flip .)@. A /module/ is either a left module or a right module. -}
data Module r m     = Module { ag :: AbelianGroup m, scale :: r -> Op1 m }
{- ^ A /vector space/ is a module over a field.

    A /homomorphism of R-modules/ or /R-linear map/ @f :: M -> M'@ is an additive homomorphism
    that also satisfies @f (r \`scale\` m) = r \`scale\` f m@. -}

type RMod           = Module
-- ^ a left module over R
type ModR           = Module
-- ^ a right module over R

pairMd              :: Module r a -> Module r b -> Module r (a, b)
-- ^ direct sum (or product) of two modules
pairMd aMd bMd      = Module (pairGp aMd.ag bMd.ag) (\r -> pairOp1 (aMd.scale r) (bMd.scale r))

mdModF              :: Module r a -> Op1 a -> Module r (Cls a)
{- ^ @mdModF md reduce@ is @md@ modulo a submodule, using @reduce@ to produce @Cls@ (coset)
    representatives. -}
mdModF (Module { .. }) reduce     =
    let modF    = Cls . reduce
    in  Module (gpModF ag reduce zeroBits) (\ r (Cls m) -> modF (scale r m))

-- ** RAlg

{- | Given a commutative ring @R@, an /R-algebra/ is a ring @A@ together with a ring
    homomorphism @R -> center(A)@. (The /center/ of a group or ring is the set of elements that
    commute with every element of the group or ring.) This makes @A@ into an @R-module@. -}
data RAlg r a       = RAlg {
    aR          :: Ring a,
    scale       :: r -> Op1 a,
    fromR       :: r -> a
}

algMd           :: RAlg r a -> Module r a
-- ^ > algMd (RAlg { .. }) = Module aR.ag scale
algMd (RAlg { .. })     = Module aR.ag scale


-- * Basic numeric rings

numAG           :: (Eq n, Num n) => AbelianGroup n
-- ^ @n@ under addition
numAG           = abelianGroup (==) (+) 0 (== 0) negate

-- ** Integer

zzAG            :: AbelianGroup Integer
-- ^ the integers ℤ under addition
zzAG            = numAG

zzDiv           :: Bool -> Integer -> Integer -> (Integer, Integer)
-- ^ integer division, rounding toward 0
zzDiv _ n d
    | d == 0    = (0, n)
    | d < 0     = let (q, r) = zzDiv False n (- d) in (- q, r)
    | otherwise = let (q, r) = divMod n d
                  in  if 2*r < d then (q, r) else (q + 1, r - d)

zzRing          :: Ring Integer
-- ^ the ring of integers ℤ
zzRing          = Ring zzAG integralDomainFlags (*) 1 id zzDiv

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

showGens                    :: (g -> String) -> [g] -> String
showGens _gShow []          = "⟨ ⟩"
showGens  gShow (g0 : gs)   = "⟨ " ++ gShow g0 ++ foldr (\g s -> ", " ++ gShow g ++ s) " ⟩" gs


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

agReads         :: forall g. AbelianGroup g -> ReadS g -> ReadS g
-- ^ read a possible sum of terms or \"-\" terms, given a function to read a single term
agReads (AbelianGroup { .. }) termReads     =
    let sumReads            :: Maybe g -> ReadS g   -- result is mg followed by s
        sumReads mg s       = case trimStart s of
                                '-':t   -> reads1 mg neg t
                                '+':t   -> reads1 mg id t
                                _       -> maybe (reads1 mg id s) (\ g -> [(g, s)]) mg
        reads1              :: Maybe g -> Op1 g -> ReadS g  -- mg + (f(next term) + rest of s)
        reads1 mg f s       = [(maybe y (y `plus`) mg, u)
                              | (x, t) <- termReads s,
                                (y, u) <- sumReads (Just (f x)) t]
    in  sumReads Nothing      -- right-associative sum for efficiency in common cases

rngReads        :: forall r. Ring r -> ReadS r -> ReadS r
{- ^ read a ring element as a sum of products or quotients of powers of \"atom\"s, given a
    function to read an \"atom\" -}
rngReads rR@(Ring { .. }) atomReads     =
    let rReads, power       :: ReadS r
        rReads      = agReads ag termReads
        power s     = do
            let t = trimStart s
            (base, u) <- case t of
                '(':_   -> readParen True rReads t
                _       -> atomReads t
            case trimStart u of
                '^':v   -> [(rExpt rR base e, w) | (e, w) <- zzReads v]
                v       -> [(base, v)]
        product2            :: (r, String) -> [(r, String)]
        product2 (r, s)     =
            case trimStart s of
                '/':u   -> concatMap (\(d, v) -> product2 (exactQuo rR r d, v)) (power u)
                u       -> case power u of
                            []  -> [(r, u)]
                            pvs -> concatMap (\(d, v) -> product2 (r `times` d, v)) pvs
        termReads s = concatMap product2 (power s)
    in  rReads

polynomReads    :: Ring p -> [(String, p)] -> ReadS p
-- ^ read a polynomial, given a list of variables. Each variable must have precedence > '^'.
polynomReads rR@(Ring { .. }) varSRs    =
    let digitsOrVarReads s  =
            let s' = trimStart s
            in  case s' of
                c:_     | isDigit c     -> [(fromZ n, t) | (n, t) <- zzReads s']
                _                       -> [(var, t)
                    | (varS, var) <- varSRs,
                      t <- maybeToList (stripPrefix varS s'),
                      null t || not (isDigit (head t))]
    in  rngReads rR digitsOrVarReads
