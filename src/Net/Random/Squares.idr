module Net.Random.Squares

import System.Random.PRNG.Squares
import Control.Monad.State

import Util

-- Squares-based

export
nextRandW : MonadState (Bits64,Bits64) m => m Bits32
nextRandW = do
  (k,c) <- get
  let (r,newc) = System.Random.PRNG.Squares.next k c
  put (k,newc)
  pure r

export
nextRand : MonadState (Bits64,Bits64) m => m Int32
nextRand = cast <$> nextRandW

export
nextRandRW : MonadState (Bits64,Bits64) m => (Bits32,Bits32) -> m Bits32
nextRandRW range = do
  (k,c) <- get
  let (r,newc) = System.Random.PRNG.Squares.nextR k c range
  put (k,newc)
  pure (cast r)

export
nextRandR : MonadState (Bits64,Bits64) m => (Int32,Int32) -> m Int32
nextRandR range = cast <$> nextRandRW (bimap cast cast range)

-- (-1,1)
export
randomNormal : MonadState (Bits64,Bits64) m => m Double
randomNormal = pure $ normalize !nextRandW

export
randomNormalR : MonadState (Bits64,Bits64) m => (Double,Double) -> m Double
randomNormalR range = pure $ normalizePR !randomNormal range

-- Brand new weight: (-8,8)
export
randomWeight : MonadState (Bits64,Bits64) m => m Double
randomWeight = pure $ !randomNormal

-- (0,1)
export
randomNormalP : MonadState (Bits64,Bits64) m => m Double
randomNormalP = pure $ normalizeP !nextRandW

-- sum 12 method of natural distribution
export
twelve : MonadState (Bits64,Bits64) m => m Double
twelve = (`subtract` 6) . sum <$> replicateA 12 randomNormalP

normalProbDense : (stdDev : Double) -> (mean : Double) -> Double -> Double
normalProbDense stdDev mean x = 1 / sqrt (2 * pi * stdDev ^ 2) * exp ((-1) * (x - mean) ^ 2 / (2 * stdDev ^ 2))

-- Perturb an existing weight
export
perturbWeight : MonadState (Bits64,Bits64) m => Double -> m Double
perturbWeight w = pure $ clamp (-1) 1 (!twelve + w)

