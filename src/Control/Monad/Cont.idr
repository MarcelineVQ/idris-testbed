module Control.Monad.Cont

-- related: Data.Container

import Control.Monad.Identity
import Control.Monad.Trans

-- can this be augmented with tracking of the depth you're working at?

public export
record ContT r m a where
  constructor MkContT
  runContT : (a -> m r) -> m r

public export
Cont : Type -> Type -> Type
Cont r a = ContT r Identity a

export
cont : ((a -> r) -> r) -> Cont r a
cont f = MkContT $ \x => Id $ f (runIdentity . x)

export
evalContT : Monad m => ContT r m r -> m r
evalContT x = runContT x pure

export
Functor (ContT r m) where
  map f fa = MkContT $ \c => runContT fa (c . f)

export
Applicative (ContT r m) where
  pure a = MkContT (\x => x a)
  f <*> fa = MkContT $ \c => runContT f $ \g => runContT fa (c . g)

export
Monad (ContT r m) where
  fa >>= f = MkContT $ \c => runContT fa $ \g => runContT (f g) c

export
MonadTrans (ContT r) where
  lift x = MkContT $ (x >>=)

export
mapContT : (m r -> m r) -> ContT r m a -> ContT r m a
mapContT f (MkContT g) = MkContT (f . g)

export
withContT : ((b -> m r) -> a -> m r) -> ContT r m a -> ContT r m b
withContT f (MkContT g) = MkContT (g . f)

export
callCC : ((a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCC f = MkContT $ \amr => runContT (f (\x => MkContT $ \_ => amr x)) amr

export
resetT : Monad m => ContT r m r -> ContT r' m r
resetT = lift . evalContT

export
shiftT : Monad m => ((a -> m r) -> ContT r m r) -> ContT r m a
shiftT f = MkContT (evalContT . f)


