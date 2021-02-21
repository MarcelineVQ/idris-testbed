module Data.Random.RVar

import Data.Random.Source

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.RWS
import Control.Monad.Either

record RVarT (m : Type -> Type) (a : Type) where
  constructor MkRVarT
  unRVarT : s -> a

runRVarTWith : RandomSource m s => RVarT m a -> s -> m a
runRVarTWith rvar s = ?sdffsdfd

-- import Control.Monad.MonadSplit

-- export
-- data RVarT : (g : Type) -> (m : Type -> Type) -> (a : Type) -> Type where
--   MkRVarT : StateT g m a -> RVarT g m a
-- 
-- export
-- unRVarT : RVarT g m a -> StateT g m a
-- unRVarT (MkRVarT s) = s
-- 
-- export
-- Functor m => Functor (RVarT m) where
--   map f = MkRVarT . map f . unRVarT
-- 
-- -- StateT in base requires Monad here
-- export
-- Monad m => Applicative (RVarT m) where
--   pure = MkRVarT . pure
--   MkRVarT f <*> MkRVarT fa = MkRVarT $ f <*> fa
-- 
-- export
-- Monad m => Monad (RVarT m) where
--   MkRVarT f >>= k = MkRVarT $ f >>= unRVarT . k
-- 
-- export
-- MonadTrans RVarT where
--   lift = MkRVarT . lift

-- interface RVarT g m a where
  -- 

-- export
-- liftRVarT : (g -> m (g,a)) -> RVarT m a
-- liftRVarT = MkRVarT . ST
-- 
-- export
-- runRVarT : RVarT g m a -> g -> m (g,a)
-- runRVarT = runStateT' . unRVarT
-- 
-- export
-- evalRVarT : Functor m => RVarT g m a -> g -> m a
-- evalRVarT m' g = snd <$> runRVarT m' g
-- 
-- export
-- execRVarT : Functor m => RVarT g m a -> g -> m g
-- execRVarT m' g = fst <$> runRVarT m' g

