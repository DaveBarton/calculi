module Data.Stack (
    Stack(..), VRStack(..)
) where

import Data.Foldable (Foldable(..))
import Data.List (uncons)
import Data.Tuple (swap)
import Data.Tuple.Extra (second)
import qualified Data.Vector as V
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL


class (Functor s, Foldable s) => Stack s where
    empty       :: s a
    (.:)        :: a -> s a -> s a  -- push
    pushRev     :: Foldable r => r a -> s a -> s a
    pop         :: s a -> Maybe (a, s a)
    
    pushRev r s     = foldl' (flip (.:)) s r

infixr 5  .:    -- same as (:)

instance Stack [] where
    empty       = []
    (.:)        = (:)
    pop         = uncons

instance Stack SL.List where
    empty       = SL.Nil
    (.:)        = (:!)
    pop         = SL.uncons

instance Stack V.Vector where
    empty       = V.empty
    (.:)        = V.cons
    pushRev     = (V.++) . V.reverse . V.fromList . toList
    pop         = V.uncons

newtype VRStack a   = VRStack { v :: V.Vector a } deriving (Eq, Show, Functor)
-- ^ A Vector-backed Stack with push/pop and left folds acting on the Right end, and right folds
-- acting on the left end.

instance Foldable VRStack where
    foldr k z rv    = foldl (flip k) z rv.v
    foldr' k z rv   = foldl' (flip k) z rv.v
    foldl k z rv    = foldr (flip k) z rv.v
    foldl' k z rv   = foldr' (flip k) z rv.v
    foldr1 k rv     = foldl1 (flip k) rv.v
    foldl1 k rv     = foldr1 (flip k) rv.v
    null rv         = null rv.v
    length rv       = length rv.v

instance Stack VRStack where
    empty       = VRStack V.empty
    a .: rv     = VRStack $ V.snoc rv.v a
    pushRev r rv    = VRStack $ rv.v V.++ V.fromList (toList r)
    pop rv      = second VRStack . swap <$> V.unsnoc rv.v
