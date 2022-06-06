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

-- public export
-- %inline
-- subtract : Neg a => Num a => a -> a -> a
-- subtract x y = x - y

export
-- %inline -- inline causes a loop currently
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
randEnv : StateT (Bits64,Bits64) IO a -> IO ()
randEnv act = do
  seed1 <- cast {from=Int32} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int32} {to=Bits64} <$> randomIO
  _ <- runStateT (seed1,seed2) $ do
    z <- act
    pure ()
  pure ()

infixl 4 &&|

export
(&&|) : Bool -> Bool -> Bool
x &&| y = x && y

infixr 10 ^
export
(^) : Num a => a -> Nat -> a
v ^ Z = 1
v ^ (S y) = v * (v ^ y)


-- TODO: bring this up with other devs for idris about it's merits and negatives
-- NB: This exists now in one form or another in base
export
total
%foreign "scheme:lambda (x) (blodwen-error-quit x)"
lie_idris_crash : String -> a

export
total
lieErrorCall : (module' : String) -> (func_name : String) -> (msg : String) -> a
lieErrorCall mod fn_name msg = lie_idris_crash $ mod ++ ":" ++ fn_name ++ ": " ++ msg
