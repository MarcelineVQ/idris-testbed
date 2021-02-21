module Data.Random.Source

public export
interface Monad m => RandomSource m s where
  getRandomWord32From : s -> m Bits32
