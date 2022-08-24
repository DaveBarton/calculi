{-# LANGUAGE NoMonoLocalBinds, PolyKinds, RankNTypes, Strict #-}

{- |  This module defines the most common types of categories, functors and universal
    properties.
    
    A /category/ of /objects/ and /arrows/ (or /morphisms/) between them generalizes the notion
    of sets (or types) and functions between them. Sometimes the objects have extra structure,
    e.g. they are groups or rings or geometric spaces, and we require the morphisms to be
    homomorphisms or \"smooth\" in some sense. Sometimes the objects and\/or arrows are either
    \"nice\" families or equivalence classes of other objects and arrows. Sometimes we turn the
    arrows around. We still require composition of arrows analogous to @.@ and \"identity\"
    arrows analogous to @id@. Such categories often accurately describe a mathematical problem
    space, and are the setting for defining and calculating homological and other properties.
    
    We say a diagram (directed graph) of objects and arrows /commutes/ if for any two paths
    with the same endpoints, the compositions of the paths are the same. Then a construction or
    map is \"natural\" if it preserves the commutativity of a specified class of diagrams, and
    is \"canonical\" if it is the unique map satisfying certain natural properties.
    
    Many algebraic computations involving elements of sets can be generalized to ones for arrows
    in categories. Equations then become commutative diagrams, and notions such as direct
    products, subsets, sets of equivalence classes, and various extensions and completions also
    have categorical generalizations. This is similar to \"point free\" notation in Haskell.
    
    Note that the objects (and arrows) in a category may have different Haskell types.
    
    This module uses LANGUAGE Strict. In particular, constructor fields are strict unless marked
    with a ~. Also, some name(s) may conflict with "Prelude" and other modules, so you may want
    to import this or those modules partially qualified.
-}

module Math.Algebra.Category.Category (
    -- * Categories and functors
    Unit1(..), Unit2(..), FlipTF(..),
    -- ** Category
    Category(..), catOpp, typesCat,
    -- ** Functor
    Functor(..), listFunctor,
    
    -- * Universal Properties
    -- $univProp
    UnivL(..), UnivR(..), InitialObj, FinalObj,
    -- ** Limits and colimits
    -- $limits
    SrcArrs2(..), SrcArrsF(..), TgtArrs2(..), TgtArrsF(..),
    
    -- * Additive categories
    AdditiveCat(..), acSum2, acIm, acCoIm
    -- ** Abelian categories
    -- $abelianCat
) where

import Prelude hiding (Functor)
import Math.Algebra.General.Algebra

import Data.Kind (Type)


-- * Categories and functors

data Unit1 a    = Unit1
-- ^ like the \"Unit\" type (), but with 1 type argument
data Unit2 a b  = Unit2
-- ^ like the \"Unit\" type (), but with 2 type arguments

newtype FlipTF f b a    = FlipTF (f a b)


-- ** Category

-- | A @(Category (.:) idArr)@
data Category (obj :: k -> Type) (arr :: k -> k -> Type)   = Category {
    catDot  :: forall a b c. arr b c -> arr a b -> arr a c,
        -- ^ @f .: (g .: h) = (f .: g) .: h@
    catId   :: forall a. obj a -> arr a a   -- ^ @(idArr t) .: f = f .: (idArr s) = f@
}

catOpp          :: Category obj arr -> Category obj (FlipTF arr)
-- ^ \"opposite category\"
catOpp cat      = Category (\ (FlipTF f) (FlipTF g) -> FlipTF (catDot cat g f))
                    (FlipTF . catId cat)

typesCat        :: Category Unit1 (->)
-- ^ the category of Haskell types and functions
typesCat        = Category (.) (const id)


-- ** Functor

-- | A @(Functor objF arrF)@ maps a @(Category obj arr)@ to a @(Category obj' arr')@ naturally.
data Functor obj arr tF obj' arr'       = Functor {
    ftrObjF :: forall a. obj a -> obj' (tF a),
    ftrArrF :: forall a b. arr a b -> arr' (tF a) (tF b)    -- ^ commutes with @.:@, takes
        -- @idArr@ to @idArr'@
}
-- ^ A /contravariant functor/ from @C@ to @D@ is a (normal \"covariant\") functor from
-- @catOpp C@ to @D@.

listFunctor     :: Functor Unit1 (->) [] Unit1 (->)
-- ^ example Functor, from typesCat to typesCat
listFunctor     = Functor (const Unit1) map


-- * Universal Properties

{- $univProp
    An object @U@ in @C@ together with extra data @x@ has a /left universal property/ if there
    is a functor @F :: C -> ((Sets))@ defining the set of legal \"extra data\" for each
    object, such that given any object @V@ together with extra data @y@, there is a unique
    morphism @f :: U -> V@ with @F(f)(x) = y@. This implies that the pair @(U, x)@ is unique
    up to isomorphism. A /right universal property/ is the dual notion (@F@ is contravariant
    and @f@ goes in the other direction). -}

data UnivL obj extr arr u       = UnivL (obj u) (extr u) (forall t. obj t -> extr t -> arr u t)
data UnivR obj extr arr u       = UnivR (obj u) (extr u) (forall a. obj a -> extr a -> arr a u)

-- | An /initial object/ in a category has a unique morphism to each object.
type InitialObj obj arr u       = UnivL obj Unit1 arr u

-- | A /final object/ in a category has a unique morphism from each object.
type FinalObj   obj arr u       = UnivR obj Unit1 arr u

-- ** Limits and colimits

{- $limits
    A map from a source object to a family of objects and arrows is a set of morphisms from
    the source object to each object in the family, commuting with the arrows in the family.
    A (categorical) /limit/ is a right universal object with this property. The dual notions
    are a map from a family of objects and arrows to a target object, and a /colimit/. -}

data    SrcArrs2 arr b c a      = SrcArrs2 (arr a b) (arr a c)
newtype SrcArrsF arr b i a      = SrcArrsF (i -> arr a b)

data    TgtArrs2 arr b c t      = TgtArrs2 (arr b t) (arr c t)
newtype TgtArrsF arr b i t      = TgtArrsF (i -> arr b t)


-- * Additive categories

{- | An @(AdditiveCat cat homAG prod2 zeroObj ~ker ~coker)@ must satisfy the axioms below. Note
    that in a general /additive category/, @ker@ and @coker@ may be undefined. -}
data AdditiveCat obj arr prod2TF z cokTF        = AdditiveCat {
    acCat       :: Category obj arr,
    
    acHomAG     :: forall a b. obj a -> obj b -> AbelianGroup (arr a b),
        -- ^ @.:@ is bilinear
    acProd2     :: forall b c.
        obj b -> obj c -> UnivR obj (SrcArrs2 arr b c) arr (prod2TF b c),
    acZeroObj   :: obj z,    -- ^ @idArr zeroObj = zero (homAG zeroObj zeroObj)@
    
    acKer       :: ~(forall b c. obj b -> obj c -> arr b c -> UnivR obj (FlipTF arr b) arr b),
        -- ^ optional; @ker(f)@ is the limit of @f, 0 :: b -> c@
    acCoker     :: ~(forall b c. obj b -> obj c -> arr b c -> UnivL obj (arr c) arr (cokTF c))
        -- ^ optional; @coker(f)@ is the colimit of @f, 0 :: b -> c@
}
-- ^ These axioms imply each @homAG(A, A)@ is a ring under @.:@, and that each @homAG(A, B)@
-- is a left module over @homAG(B, B)@ and a right module over @homAG(A, A)@.

acSum2          :: AdditiveCat obj arr prod2TF z cokTF ->
    obj b -> obj c -> UnivL obj (TgtArrs2 arr b c) arr (prod2TF b c)
acSum2 (AdditiveCat (Category (.:) idArr) homAG prod2 _ _ _) bObj cObj  =
    UnivL bcObj (TgtArrs2 bToBc cToBc) sumUnivF
  where UnivR bcObj (SrcArrs2 bcToB bcToC) prodUnivF    = prod2 bObj cObj
        bToBc   = prodUnivF bObj (SrcArrs2 (idArr bObj) (agZero (homAG bObj cObj)))
        cToBc   = prodUnivF cObj (SrcArrs2 (agZero (homAG cObj bObj)) (idArr cObj))
        sumUnivF tObj (TgtArrs2 bToT cToT)  =
            agPlus (homAG bcObj tObj) (bToT .: bcToB) (cToT .: bcToC)

acIm            :: AdditiveCat obj arr prod2TF z cokTF ->
        obj b -> obj c -> arr b c -> UnivR obj (FlipTF arr c) arr c
-- ^  @image(f) = ker(coker(f))@, assuming the @ker@ and @coker@ are both defined
acIm (AdditiveCat _ _ _ _ ker coker) bObj cObj f        = ker cObj ckObj ckF
  where UnivL ckObj ckF _   = coker bObj cObj f

acCoIm          :: AdditiveCat obj arr prod2TF z cokTF ->
        obj b -> obj c -> arr b c -> UnivL obj (arr b) arr (cokTF b)
-- ^  @coimage(f) = coker(ker(f))@, assuming the @coker@ and @ker@ are both defined
acCoIm (AdditiveCat _ _ _ _ ker coker) bObj cObj f      = coker kObj bObj kF
  where UnivR kObj (FlipTF kF) _    = ker bObj cObj f

-- ** Abelian categories

{- $abelianCat An /Abelian category/ is an additive category where @ker@ and @coker@ must be
    defined for all arrows @f@, and the natural map @image(f) -> coimage(f)@ is an
    isomorphism (has a two-sided inverse). -}

-- @@ AbelCat isom. inv.?? & examples
-- @@ LiberalTypeSynonyms? ImpredicativeTypes? ExistentialQuantification??
