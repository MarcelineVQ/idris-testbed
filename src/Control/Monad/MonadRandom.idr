module Control.Monad.MonadRandom

import System.Random

import Data.List.Lazy

interface Monad m => MonadRandom m where
  getRandomR : Random a => (a, a) -> m a
  getRandom : Random a => m a
  getRandomRs : Random a => (a, a) -> m (LazyList a)
  getRandoms : Random a => m (LazyList a)

-- MonadRandom IO where
  -- 
