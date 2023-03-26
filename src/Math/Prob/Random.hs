module Math.Prob.Random {- @@() -} where

import Data.List (unfoldr)
import System.Random (RandomGen)


type RandomF a  = forall g. RandomGen g => g -> (a, g)
-- ^ abstractly a probability distribution

randomsBy       :: RandomGen g => RandomF a -> g -> [a]
randomsBy r     = unfoldr (Just . r)


-- @@ unfinished, incl. make/doc Strict? LiberalTypeSynonyms?
