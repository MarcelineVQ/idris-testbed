module System.Random.RandomGen

interface RandomGen g a where
  next : g -> (a,g)
