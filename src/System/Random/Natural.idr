module System.Random.Natural

import public System.Random

-- natural/gaussian distribution

public export
replicateA : Applicative f => Nat -> f a -> f (List a)
replicateA Z _ = pure []
replicateA (S k) act = [| act :: replicateA k act |]

public export
subtract : Neg a => Num a => a -> a -> a
subtract x y = x - y

-- (n,m) rather than [n,m]
export
notinclusive : (Ord a, Random a) => HasIO io => (a,a) -> io a
notinclusive (m,n) = do
  x <- randomRIO (m,n)
  if x <= m || x >= n
    then notinclusive (m,n)
    else pure x

-- sum 12 method
export
twelve : (Random a, Neg a, Ord a) => HasIO io => io a
twelve = (`subtract` 6) . sum <$> replicateA 12 (notinclusive {a} (0,1))

-- polar method, Double due to sqrt/log
export
polar : HasIO io => io (Double,Double)
polar = do
  u <- notinclusive {a=Double} (-1,1)
  v <- notinclusive {a=Double} (-1,1)
  let s = u*u + v*v
  if s >= 1
    then polar
    else let x = u * sqrt (log s * negate 2 / s)
             y = v * sqrt (log s * negate 2 / s)
         in pure (x,y)



