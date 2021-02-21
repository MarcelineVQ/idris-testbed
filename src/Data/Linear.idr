module Data.Linear

import Data.Vect

dot : Num a => Vect n a -> Vect n a -> a
dot [] [] = 0
dot (x :: xs) (y :: ys) = x * y + dot xs ys

-- dot with bias
dot1 : Num a => Vect n a -> Vect (S n) a -> a
dot1 [] [y] = y
dot1 (x :: xs) (y :: ys) = x * y + dot1 xs ys
