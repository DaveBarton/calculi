{-# LANGUAGE Strict #-}

{- This internal module "StrictList2" extends "StrictList". Ideally the two should be merged,
    and possibly renamed to "Data.List.Strict". They are normally imported qualified. Note that
    to import only @pattern (:!)@ unqualified, the importing module apparently needs to enable
    @PatternSynonyms@.
    
    Note that this module uses LANGUAGE Strict. Be mindful of this when changing or merging this
    module.
-}

module StrictList2 (
    module StrictList, pattern (:!), headMaybe, singleton, fromList, zipWithReversed,
    partitionReversed, eqBy, lexCmpBy, mergeBy, minusSorted, insertBy, deleteBy
) where

import Prelude hiding (reverse, take, drop, filter, takeWhile, dropWhile, span, break)
import StrictList hiding (head, tail, last, init)   -- these 4 functions have nonstandard
    -- definitions when applied to the empty list

import Math.Algebra.General.Algebra


pattern (:!)        :: a -> List a -> List a
infixr 5  :!        -- same fixity as (:)
pattern h :! t      = Cons h t
{-# INLINE (:!) #-}

{-# COMPLETE (:!), Nil #-}


headMaybe           :: List a -> Maybe a
headMaybe (h :! _)  = Just h
headMaybe Nil       = Nothing

singleton           :: a -> List a
singleton e         = e :! Nil

fromList            :: [a] -> List a
-- ^ 'fromListReversed' is faster, so better when convenient
fromList            = reverse . fromListReversed

zipWithReversed     :: (a -> b -> c) -> List a -> List b -> List c
zipWithReversed f   = go Nil
  where
    go r (a :! as) (b :! bs)    = go (f a b :! r) as bs
    go r _         _            = r

partitionReversed   :: Pred a -> List a -> (List a, List a)
partitionReversed p = go Nil Nil    -- would using foldl' be slower?
  where
    go rts rfs (x :! t)     = if p x then go (x :! rts) rfs t else go rts (x :! rfs) t
    go rts rfs _            = (rts, rfs)

eqBy                :: EqRel a -> EqRel (List a)
eqBy aEq            = go
  where
    go (x :! ~t) (y :! ~u)  = aEq x y && go t u
    go Nil       Nil        = True
    go _         _          = False

lexCmpBy            :: Cmp a -> Cmp (List a)
lexCmpBy aCmp       = go
  where
    go (x :! ~t) (y :! ~u)  = aCmp x y <> go t u
    go Nil       Nil        = EQ
    go Nil       _          = LT
    go _         Nil        = GT

mergeBy             :: Cmp a -> Op2 (List a)
-- like 'mergeBy' in Data.List.Extra
mergeBy cmp         = go Nil
  where
    go r xs@(x :! ~t) ys@(y :! ~u)  =
        if cmp x y /= GT
        then go (x :! r) t  ys
        else go (y :! r) xs u
    go r xs           Nil           = prependReversed r xs
    go r Nil          ys            = prependReversed r ys

minusSorted         :: Cmp a -> Op2 (List a)
-- difference of two sorted lists, like 'minusBy' from data-ordlist
minusSorted cmp     = go Nil
  where
    go r xs@(x :! ~t) ys@(y :! ~u)  =
        case cmp x y of
           LT   -> go (x :! r) t  ys
           EQ   -> go r        t  u
           GT   -> go r        xs u
    go r xs           Nil           = prependReversed r xs
    go r Nil          _ys           = reverse r

insertBy            :: Cmp a -> a -> Op1 (List a)
insertBy cmp x      = go Nil
  where
    go r ys@(h :! ~t)   = case cmp x h of
        GT  -> go (h :! r) t
        _   -> prependReversed r (x :! ys)
    go r Nil            = prependReversed r (singleton x)

deleteBy            :: EqRel a -> a -> Op1 (List a)
deleteBy eq x       = go Nil
  where
    go r (h :! ~t)  = if x `eq` h then prependReversed r t else go (h :! r) t
    go r Nil        = reverse r
