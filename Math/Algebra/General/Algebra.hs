{-# LANGUAGE Strict #-}

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
    -- * Basic predicate and operation types - 'Pred', 'Op1', 'Op2'
    assert,
    Pred,
    Op1, pairOp1,
    Op2, pairOp2,
    (.*), on,
    (!$),
    
    -- * Equivalence relations and classes - 'EqRel', 'Cls'
    EqRel,
    pairEq, liftEq,
    Cls(..),
    
    -- * Comparison - 'Cmp'
    Cmp,
    cmpEq,
    maxBy, minBy,
    lex2Cmp, liftCompare,
    
    -- * Groups defined - 'Group'
    Group(..),
    pairGp, gpModF,
    
    -- * Abelian groups defined - 'AbelianGroup'
    AbelianGroup, agPlus, agZero, isZero, agNeg,
    nonzeroQ, minus,
    
    -- * Rings and fields defined - 'Ring', 'Field'
    Ring(..), Field,
    rEq, rPlus, rZero, rIsZero, rNeg,
    rOneQ, exactQuo, nearQuo, smallRem, rInv, divides,
    expt1, exptR,
    divisionRing, fieldGcd,
    
    -- * Modules and R-algebras defined - 'Module', 'RMod', 'ModR', 'RAlg'
    Module(..), RMod, ModR,
    pairMd, mdModF,
    RAlg(..),
    algMd,
    
    -- * Basic numeric rings - @Integer@, @Double@
    zzAG, zzDiv2, zzRing,
    dblAG, dblRing,
    
    -- * Implicit algebras - 'ImpAG', 'ImpRing'
    ImpAG(..), ImpRing(..),
    
    -- * Converting \<-> String
    plusS, timesS, quoS,
    Prec, applPrec, exptPrec, multPrec, addPrec, ShowPrec,
    trimStart,
    agReads, rngReads, polynomReads
) where

import Control.Exception (assert)
import Data.Char (isDigit)
import Data.Function (on)
import Data.Functor.Classes (liftCompare, liftEq)
import Data.List (stripPrefix)
import Data.List.Extra (trimStart)
import Data.Maybe (maybeToList)
import Text.ParserCombinators.ReadPrec (Prec)


-- * Basic predicate and operation types - 'Pred', 'Op1', 'Op2'

type Pred a     = a -> Bool
-- ^ a predicate

type Op1 a      = a -> a

pairOp1         :: (a -> a') -> (b -> b') -> (a, b) -> (a', b')
-- ^ componentwise function; e.g. @Op1 a -> Op1 b -> Op1 (a, b)@
pairOp1 f g (x, y)  = (f x, g y)

type Op2 a      = a -> a -> a

pairOp2         :: (a -> a' -> a'') -> (b -> b' -> b'') -> (a, b) -> (a', b') -> (a'', b'')
-- ^ componentwise function; e.g. @Op2 a -> Op2 b -> Op2 (a, b)@
pairOp2 f g (x, y) (u, v)   = (f x u, g y v)

(.*)            :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
-- ^ composition; cf. @Data.Function.on :: (b -> b -> c) -> (a -> b) -> (a -> a -> c)@
(f .* g) x y    = f (g x y)

infixr 9 .*     -- for mixing with @.@

(!$)            :: (a -> b) -> a -> b
(!$)            = ($!)
infixl 0 !$     -- for strict applications of functions with > 1 arg


-- * Equivalence relations and classes - 'EqRel', 'Cls'

type EqRel a    = a -> a -> Bool
{- ^  An /equivalence relation/ \"=\" must abstractly satisfy @x = x@, @x = y => y = x@ and
    @x = y && y = z => x = z@. An @eq :: EqRel a@ attempts to implement such a relation, and
    must satisfy @eq x y => x = y@. If the converse is true, we say @eq@ (or @a@) is
    /discrete/.  -}

pairEq          :: EqRel a -> EqRel b -> EqRel (a, b)
pairEq aEq ~bEq (x, ~y) (u, ~v)     = aEq x u && bEq y v


newtype Cls a   = Cls { clsRep :: a }   deriving (Eq, Ord)
-- ^ @(Cls r)@ represents the class of elements \"equivalent\" to @r@ (according to a specified
-- equivalence relation). Usually we require @r@ to be \"simple\" or \"normalized\" in some
-- way.


-- * Comparison - 'Cmp'

type Cmp a      = a -> a -> Ordering
{- ^  A /total ordering/ is antisymmetric and transitive.  -}

cmpEq           :: Cmp a -> EqRel a
cmpEq cmp x y   = cmp x y == EQ

maxBy, minBy    :: Cmp a -> Op2 a
maxBy cmp x y   = if cmp x y /= GT then y else x
minBy cmp x y   = if cmp x y /= GT then x else y

lex2Cmp         :: Cmp a -> Cmp b -> Cmp (a, b)
lex2Cmp aCmp ~bCmp (x, ~y) (u, ~v)  = let d = aCmp x u in if d /= EQ then d else bCmp y v


-- * Groups defined - 'Group'

-- | @(Group eq op ident isIdent inv)@ is defined below. It generalizes the set of symmetries of
-- a structure (such as reflection, rotation, translation), where symmetries can be composed and
-- inverted.
data Group g    = Group {
    gpEq    :: EqRel g,
    gpOp    :: Op2 g,       -- ^ @op@ is well defined & associative
    gpId    :: g,           -- ^ @(ident \`op\`) = (\`op\` ident) = id@
    gpIsId  :: Pred g,      -- ^ @isIdent x = ident \`eq\` x@ for all @x@
    gpInv   :: Op1 g        -- ^ @(inv x) \`op\` x = x \`op\` (inv x) = ident@ for all @x@;
        -- therefore @inv@ is well defined also
}
-- ^ A /homomorphism of groups/ is a well defined function @f :: G -> G'@ that satisfies
-- @f (op x y) = op' (f x) (f y)@. This implies @f ident = ident'@, and
-- @f (inv x) = inv' (f x)@.

pairGp          :: Group a -> Group b -> Group (a, b)
-- ^ direct product group
pairGp aGp bGp  =
    Group (pairEq (gpEq aGp) (gpEq bGp))
          (pairOp2 (gpOp aGp) (gpOp bGp))
          (gpId aGp, gpId bGp)
          (\ (a, ~b) -> gpIsId aGp a && gpIsId bGp b)
          (pairOp1 (gpInv aGp) (gpInv bGp))

gpModF          :: Group g -> Op1 g -> Group (Cls g)
-- ^ @gpModF gp reduce@ is @gp@ modulo a normal subgroup, using @reduce@ to produce @Cls@
-- (coset) representatives.
gpModF (Group eq op ident isIdent inv) reduce   =
    let modF    = Cls . reduce
        redId   = reduce ident
    in  Group (eq `on` clsRep) (modF .* (op `on` clsRep)) (Cls redId)
            ((if isIdent redId then isIdent else eq redId) . clsRep)
            (modF . inv . clsRep)


-- * Abelian groups defined - 'AbelianGroup'

type AbelianGroup       = Group
-- ^ @op@ must be commutative
agPlus          :: AbelianGroup a -> Op2 a
agPlus          = gpOp
agZero          :: AbelianGroup a -> a
agZero          = gpId
isZero          :: AbelianGroup a -> Pred a
isZero          = gpIsId
agNeg           :: AbelianGroup a -> Op1 a
agNeg           = gpInv

nonzeroQ        :: AbelianGroup a -> Pred a
nonzeroQ ag     = not . isZero ag     -- @@@ does omitting x slow down katsura6 ??

minus           :: AbelianGroup a -> Op2 a
minus (Group _ (+:) _ _ neg) x y        = x +: neg y


-- * Rings and fields defined - 'Ring', 'Field'

-- | @(Ring ag (*:) one fromZ div2)@ is defined below.
data Ring a     = Ring {
    rAG     :: AbelianGroup a,
    rTimes  :: Op2 a,       -- ^ @(*:)@ is well defined & distributes over @plus@ & is normally
        -- associative
    rOne    :: a,           -- ^ @(one *:) = (*: one) = id@
    -- @@@ rOneQ below -> rIsOne here !?
    rFromZ  :: Integer -> a,    -- the unique Ring homomorphism from Z to this Ring
    rDiv2   :: Bool -> a -> a -> (a, a)     -- ^ @div2 doFull x y = (q, r) => x = q*y + r@ and
        -- @r@'s \"size\" is (attempted to be) minimized. If @doFull@, then all of @r@ is
        -- minimized; else just its \"topmost\" nonzero \"term\" is. (Words such as \"size\"
        -- have meanings that vary by context. Also in general, the results of @div2@ may not be
        -- uniquely determined by these requirements.)
}
-- ^ A ring is /commutative/ if @*:@ is. A /unit/ is an element @x@ such that there exists a
-- @y@ with @x *: y = y *: x = one@. A /division ring/ is a ring with @zero \/= one@ and in
-- which every non-zero element is a unit. A /field/ is a commutative division ring.
--
-- A /homomorphism of rings/ @f :: R -> R'@ is an additive (Abelian group) homomorphism that
-- also satisfies @f (x *: y) = f x *:' f y@ and @f one = one'@.

type Field      = Ring

rEq             :: Ring a -> EqRel a
rEq             = gpEq . rAG
rPlus           :: Ring a -> Op2 a
rPlus           = agPlus . rAG
rZero           :: Ring a -> a
rZero           = agZero . rAG
rIsZero         :: Ring a -> Pred a
rIsZero         = isZero . rAG
rNeg            :: Ring a -> Op1 a
rNeg            = agNeg . rAG

rOneQ           :: Ring a -> Pred a
rOneQ aR        = rEq aR (rOne aR)

exactQuo        :: Ring a -> Op2 a
exactQuo (Ring ag _ _ _ div2) x y       =
    let (q, r)  = div2 False x y
    in  assert (isZero ag r) q

nearQuo, smallRem       :: Ring a -> Bool -> Op2 a
nearQuo rR doFull x y   = fst (rDiv2 rR doFull x y)
smallRem rR doFull x y  = snd (rDiv2 rR doFull x y)

rInv            :: Ring a -> Op1 a
rInv rR         = exactQuo rR (rOne rR)

divides         :: Ring a -> a -> a -> Bool
-- ^ note the arguments are reversed from division
divides (Ring ag _ _ _ div2) d x    = isZero ag (snd (div2 False x d))

expt1           :: (Integral b) => Op2 a -> a -> b -> a
-- ^ exponent \>= 1
expt1 (*:) x n
    | n == 1    = x
    | odd n     = x *: expt1 (*:) x (n - 1)
    | otherwise = assert (n > 1) $ expt1 (*:) (x *: x) (n `quot` 2)
{-# SPECIALIZE expt1 :: Op2 a -> a -> Int -> a #-}

exptR           :: (Integral b) => Ring a -> a -> b -> a
exptR rR x n
    | n > 0     = expt1 (rTimes rR) x n
    | n == 0    = rOne rR
    | otherwise = rInv rR (exptR rR x (- n))
{-# SPECIALIZE exptR :: Ring a -> a -> Int -> a #-}

divisionRing    :: AbelianGroup a -> Op2 a -> a -> (Integer -> a) -> Op1 a -> Ring a
divisionRing ag (*:) one fromZ inv      =
    let zero        = agZero ag
        div2 _ x y  = if isZero ag y then (zero, x) else (x *: inv y, zero)
    in  Ring ag (*:) one fromZ div2

fieldGcd        :: Field a -> Op2 a
fieldGcd (Ring ag _ one _ _) x y    = if isZero ag x && isZero ag y then agZero ag else one


-- * Modules and R-algebras defined - 'Module', 'RMod', 'ModR', 'RAlg'

-- | Given an Abelian group G, End(G) = { endomorphisms of G } = { homomorphisms G -> G } is a
-- ring, with @*:@ given by composition. Given a ring R, a /left module over R/ is an Abelian
-- group M together with a ring homomorphism R -> End(M). A /right module over R/ has the same
-- definition, but with function composition defined on the right, i.e. by @(flip .)@.
data Module r m = Module { mdAG :: AbelianGroup m, mdScale :: r -> Op1 m }
-- ^ A /vector space/ is a module over a field.
--
-- A /homomorphism of R-modules/ or /R-linear map/ @f :: M -> M'@ is an additive homomorphism
-- that also satisfies @f (r \`scale\` m) = r \`scale\` f m@.

type RMod       = Module
-- ^ left module over R
type ModR       = Module
-- ^ right module over R

pairMd          :: Module r a -> Module r b -> Module r (a, b)
-- ^ direct sum (or product) module
pairMd aMd bMd  =
    Module (pairGp (mdAG aMd) (mdAG bMd)) (\r -> pairOp1 (mdScale aMd r) (mdScale bMd r))

mdModF          :: Module r a -> Op1 a -> Module r (Cls a)
-- ^ @mdModF md reduce@ is @md@ modulo a submodule, using @reduce@ to produce @Cls@ (coset)
-- representatives.
mdModF (Module ag scale) reduce =
    let modF    = Cls . reduce
    in  Module (gpModF ag reduce) (\ r (Cls m) -> modF (scale r m))


-- | Given a commutative ring @R@, an /R-algebra/ is a ring @A@ together with a ring
-- homomorphism @R -> center(A)@. (The /center/ of a group or ring is the set of elements that
-- commute with every element of the group or ring.)  This makes @A@ into an @R-module@.
data RAlg r a   = RAlg {
    algRing     :: Ring a,
    algScale    :: r -> Op1 a,
    algFromR    :: r -> a
}

algMd           :: RAlg r a -> Module r a
algMd (RAlg aRing scale _)      = Module (rAG aRing) scale


-- * Basic numeric rings - @Integer@, @Double@

zzAG            :: AbelianGroup Integer
zzAG            = Group (==) (+) 0 (== 0) negate

zzDiv2          :: Bool -> Integer -> Integer -> (Integer, Integer)
zzDiv2 _ n d
    | d == 0    = (0, n)
    | d < 0     = let (q, r) = zzDiv2 False n (- d) in (- q, r)
    | otherwise = let (q, r) = divMod n d
                  in  if 2*r < d then (q, r) else (q + 1, r - d)

zzRing          :: Ring Integer
zzRing          = Ring zzAG (*) 1 id zzDiv2


dblAG           :: AbelianGroup Double
dblAG           = Group (==) (+) 0 (== 0) negate

dblRing         :: Field Double
dblRing         = divisionRing dblAG (*) 1 fromInteger recip


-- * Implicit algebras - 'ImpAG', 'ImpRing'

class ImpAG a where
    impAG       :: AbelianGroup a
    
    (==.)       :: EqRel a
    (+.), (-.)  :: Op2 a
    imp0        :: a
    impIs0      :: Pred a
    impNeg      :: Op1 a
    
    (==.)       = gpEq impAG
    (+.)        = agPlus impAG
    imp0        = agZero impAG
    impIs0      = isZero impAG
    impNeg      = agNeg impAG
    (-.)        = minus impAG

class ImpAG a => ImpRing a where
    impRing     :: Ring a
    
    (*.)        :: Op2 a
    imp1        :: a
    impFromZ    :: Integer -> a
    impDiv2     :: Bool -> a -> a -> (a, a)
    
    -- impAG       = rAG impRing    -- Haskell doesn't allow this
    
    (*.)        = rTimes impRing
    imp1        = rOne impRing
    impFromZ    = rFromZ impRing
    impDiv2     = rDiv2 impRing


-- * Converting \<-> String

plusS           :: String -> String -> String   -- ^ caller checks precedences
plusS s t       = if s == "0" then t else case t of
    "0"         -> s
    '-':_       -> s ++ t
    _           -> s ++ '+' : t

timesS          :: String -> String -> String   -- ^ caller checks precedences
timesS s t
    | null t || t == "1"    = s
    | s == "1"              = t
    | s == "0" || t == "0"  = "0"
    | s == "-1"             = '-' : t
    | otherwise             = s ++ t

quoS            :: String -> String -> String   -- ^ caller checks precedences
quoS s t        = if t == "1" || s == "0" then s else s ++ '/' : t


applPrec, exptPrec, multPrec, addPrec     :: Prec
applPrec        = 10
exptPrec        = 8
multPrec        = 7
addPrec         = 6

type ShowPrec a = Prec -> a -> String


agReads         :: AbelianGroup g -> ReadS g -> ReadS g
agReads gAG termReads   =
    let sumReads mg s       = case trimStart s of
                                '-':t   -> reads1 mg (agNeg gAG) t
                                '+':t   -> reads1 mg id t
                                _       -> maybe (reads1 mg id s) (\ g -> [(g, s)]) mg
        reads1 mg f s       = [(maybe y (agPlus gAG y) mg, u)
                              | (x, t) <- termReads s,
                                (y, u) <- sumReads (Just (f x)) t]
    in  sumReads Nothing      -- right-associative sum for common efficiency

rngReads        :: Ring r -> ReadS r -> ReadS r
rngReads rR atomReads   =
    let rReads      = agReads (rAG rR) termReads
        power s     = do
            let t = trimStart s
            (base, u) <- case t of
                '(':_   -> readParen True rReads t
                _       -> atomReads t
            case trimStart u of
                '^':v   -> [(exptR rR base (e :: Integer), w) | (e, w) <- reads v]
                v       -> [(base, v)]
        product2 (r, s)  =
            case trimStart s of
                '/':u   -> concatMap (\(d, v) -> product2 (exactQuo rR r d, v)) (power u)
                u       -> case power u of
                            []  -> [(r, u)]
                            pvs -> concatMap (\(d, v) -> product2 (rTimes rR r d, v)) pvs
        termReads s = concatMap product2 (power s)
    in  rReads

polynomReads    :: Ring p -> [(String, p)] -> ReadS p   -- ^ varSs have precedence > '^'
polynomReads pR varSRs  =
    let digitsOrVarReads s  =
            let s' = trimStart s
            in  case s' of
                c:_     | isDigit c     -> [(rFromZ pR n, t) | (n, t) <- reads s']
                _                       ->
                    [(var, t) | (varS, var) <- varSRs, t <- maybeToList (stripPrefix varS s')]
    in  rngReads pR digitsOrVarReads
