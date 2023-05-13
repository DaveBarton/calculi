module Data.Stack (
    Stack(..), RVector(..)
) where

import Data.Foldable (Foldable(..))
import Data.List (uncons)
import Data.Tuple (swap)
import Data.Tuple.Extra (second)
import qualified Data.Vector as V
import StrictList2 (pattern (:!))
import qualified StrictList2 as SL


class Foldable s => Stack s where
    empty       :: s a
    push        :: a -> s a -> s a
    pushRev     :: Foldable r => r a -> s a -> s a
    pop         :: s a -> Maybe (a, s a)
    
    pushRev r s     = foldl' (flip push) s r

instance Stack [] where
    empty       = []
    push        = (:)
    pop         = uncons

instance Stack SL.List where
    empty       = SL.Nil
    push        = (:!)
    pop         = SL.uncons

instance Stack V.Vector where
    empty       = V.empty
    push        = V.cons
    pushRev     = (V.++) . V.reverse . V.fromList . toList
    pop         = V.uncons

newtype RVector a   = RVector { v :: V.Vector a }
-- ^ A Vector with push/pop and left folds acting on the Right end, and right folds acting on
-- the left end.

instance Foldable RVector where
    foldr k z rv    = foldl (flip k) z rv.v
    foldr' k z rv   = foldl' (flip k) z rv.v
    foldl k z rv    = foldr (flip k) z rv.v
    foldl' k z rv   = foldr' (flip k) z rv.v
    foldr1 k rv     = foldl1 (flip k) rv.v
    foldl1 k rv     = foldr1 (flip k) rv.v
    null rv         = null rv.v
    length rv       = length rv.v

instance Stack RVector where
    empty       = RVector V.empty
    push a rv   = RVector $ V.snoc rv.v a
    pushRev r rv    = RVector $ rv.v V.++ V.fromList (toList r)
    pop rv      = second RVector . swap <$> V.unsnoc rv.v
