module Net.Random.IO

import System.Random

import Util

-- (n,m) rather than [n,m]
export
notinclusive : (Ord a, Random a) => HasIO io => (a,a) -> io a
notinclusive (m,n) = do
  x <- randomRIO (m,n)
  if x <= m || x >= n
    then notinclusive (m,n)
    else pure x

-- sum 12 method of natural distribution
-- export
-- twelve : MonadState (Bits64,Bits64) m => m Double
-- twelve = (`subtract` 6) . sum <$> replicateA 12 randomNormalP

-- sum 12 method
export
twelve : (Random a, Neg a, Ord a) => HasIO io => io a
twelve = (`subtract` 6) . sum <$> replicateA 12 (notinclusive {a} (0,1))

-- Perturb an existing weight
export
perturbWeight : HasIO io => Double -> io Double
perturbWeight w = pure $ clamp (-8) 8 (!twelve + w)

-- Brand new weight
export
randWeight : HasIO io => io Double
randWeight = randomRIO (-8,8)
