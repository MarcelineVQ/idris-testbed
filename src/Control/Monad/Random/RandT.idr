module Control.Monad.Random.RandT

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Either

-- import Control.Monad.MonadSplit

export
data RandT : (g : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
  MkRandT : StateT g m a -> RandT g m a

export
unRandT : RandT g m a -> StateT g m a
unRandT (MkRandT s) = s

export
Functor m => Functor (RandT g m) where
  map f = MkRandT . map f . unRandT

-- StateT in base requires Monad here
export
Monad m => Applicative (RandT g m) where
  pure = MkRandT . pure
  MkRandT f <*> MkRandT fa = MkRandT $ f <*> fa

export
Monad m => Monad (RandT g m) where
  MkRandT f >>= k = MkRandT $ f >>= unRandT . k

export
MonadTrans (RandT g) where
  lift = MkRandT . lift

-- interface RandT g m a where
  -- 

export
liftRandT : (g -> m (g,a)) -> RandT g m a
liftRandT = MkRandT . ST

export
runRandT : RandT g m a -> g -> m (g,a)
runRandT = runStateT' . unRandT

export
evalRandT : Functor m => RandT g m a -> g -> m a
evalRandT m' g = snd <$> runRandT m' g

export
execRandT : Functor m => RandT g m a -> g -> m g
execRandT m' g = fst <$> runRandT m' g
