module Util

import Data.List
import Control.Monad.State
import System.Random

public export
replicateA : Applicative f => Nat -> f a -> f (List a)
replicateA Z _ = pure []
replicateA (S k) act = [| act :: replicateA k act |]

public export
liftA2 : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x y = [| f x y |]

public export
%inline
subtract : Neg a => Num a => a -> a -> a
subtract x y = x - y

export
%inline
exp : (Num a, Ord b, Neg b) => a -> b -> a
exp x y = if y <= 0 then 1 else x * exp x (y - 1)

export
%inline
squared : Num a => a -> a
squared x = x*x

export
%inline
clamp : Ord a => a -> a -> a -> a
clamp min max v = if v > max then max else if v < min then min else v

export
maximum : (Ord a, Foldable f) => f a -> Maybe a
maximum = foldr (\a,as => case as of Nothing => Just a; Just x => Just (max a x)) Nothing

export
%inline
sortOn : (Ord b) => (a -> b) -> List a -> List a
sortOn f xs = sortBy (comparing f) xs

export
%inline
[Down] (ord : Ord a) => Ord a where
  compare x y = compare @{ord} y x

export
randEnv : MonadState (Bits64,Bits64) IO => IO a -> IO ()
randEnv act = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  _ <- runStateT (seed1,seed2) $ lift act
  pure ()
