module Math.Prob.Random (
    RandomGen, SplitGen, splitGen,
    RandomF1, RandomF2, randomF1To2, randomsBy,
    randomIndsDistinct
) where

import Data.Bifunctor (first)
import Data.Containers.ListUtils (nubInt)
import Data.List (unfoldr)
import System.Random (RandomGen, SplitGen, splitGen, uniformRs, uniformShuffleList)


{- $splittable
    Fast splittable pseudo-random number generators are sometimes needed for pure code. However,
    current ones are not cryptographically secure. This is ok though for most mathematical
    algorithms. -}

type RandomF1 g a   = g -> a
{- ^ abstractly a probability distribution, for a 'RandomGen' @g@ (which may have to be a
    'SplitGen') -}

type RandomF2 g a   = g -> (a, g)
{- ^ abstractly a probability distribution, for a 'RandomGen' @g@ (which may have to be a
    'SplitGen') -}

randomF1To2     :: SplitGen g => RandomF1 g a -> RandomF2 g a
-- ^ for a splittable random number generator, convert a 'RandomF1' to a 'RandomF2'
randomF1To2 r   = first r . splitGen

randomsBy       :: RandomGen g => RandomF2 g a -> g -> [a]
-- ^ an infinite list of random elements
randomsBy r     = unfoldr (Just . r)


randomIndsDistinct  :: RandomGen g => Int -> Int -> g -> [Int]
{- ^ @randomIndsDistinct n k g@ returns @k@ distinct random numbers @i@, with @0 <= i < n@ for
    each @i@, aka \"choosing without replacement\". This assumes @0 <= k <= n@. -}
randomIndsDistinct n k g
    | not (0 <= k && k <= n)        = error "randomIndsDistinct - invalid arguments"
    | k < n `quot` 4 {- tune? -}    = take k (nubInt (uniformRs (0, n - 1) g))
    | otherwise                     = take k (fst (uniformShuffleList [0 .. n - 1] g))


-- @@ unfinished, incl. make/doc Strict?
