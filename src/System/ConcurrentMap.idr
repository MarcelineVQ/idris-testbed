module System.ConcurrentMap

import Data.IORef
import Data.List -- splitAt

import System.Info -- getNProcessors
import Data.Maybe

worker : IO b -> IORef (Maybe b) -> IO (ThreadID, IORef (Maybe b))
worker act ref = do
  t <- fork (act >>= writeIORef ref . Just)
  pure (t,ref)

export
chunksOf : Nat -> List a -> List (List a)
chunksOf Z xs = [xs] -- NB: Differs from some implementations where this is []
chunksOf _ [] = []
chunksOf k xs = let (r,s) = splitAt k xs
                in r :: chunksOf k s

export
||| Best default for threads is your computer's thread count, including hyperthreads.
mapNConcurrently : (threads : Nat) -> (a -> IO b) -> List a -> IO (List b)
mapNConcurrently i f xs = do
  Just res <- map sequence $ for (chunksOf i xs) $ \chunk => do
      futures <- for chunk $ \x => newIORef Nothing >>= worker (f x)
      map sequence $ for futures $ \(t,ref) => do
        threadWait t
        readIORef ref
    | Nothing => pure [] -- shouldn't happen, we don't allow a way for Nothing to occur
  pure (concat res)

export
%inline
mapConcurrently : (a -> IO b) -> List a -> IO (List b)
mapConcurrently f xs = mapNConcurrently (fromMaybe 8 (!getNProcessors)) f xs
