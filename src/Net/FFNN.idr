module Net.FFNN

import Net.Random.IO

import Control.Monad.Random.RandT

import Data.IOMatrix

import Data.Strong.IOMatrix
import Data.Strong.IOArray

import System.Random.Natural

import System.Random.PRNG.Squares

import Net.Activations

import Util

-- I want to predict what x bars from now will be, lets say 10 bars
-- most direct choice is feed-forward on 100 bars at once, with
-- high,low,open,close per bar. This means our input layer is 400 wide
public export
record Weights (i : Nat) (o : Nat) where
  constructor MkWeights
  wBias : SIOArray o Double
  wNodes : SIOMatrix o i Double


{-
Now, a Weights linking an m-node layer to an n-node layer has an n-dimensional
bias vector (one component for each output) and an n-by-m node weight matrix
(one column for each output, one row for each input).
-}
public export
data Network : Nat -> List Nat -> Nat -> Type where
  O : Weights i o -> Network i [] o
  L : Weights i h -> Network h hs o -> Network i (h :: hs) o

export
randomArr : HasIO io => (s : Nat) -> io (SIOArray s Double)
randomArr s = newArrayFillM s (\_ => randWeight)

export
randomMat : HasIO io => (m,n : Nat) -> io (SIOMatrix m n Double)
randomMat m n = newFillM (cast m) (cast n) (\_,_ => randWeight)

export
randomWeights : HasIO io => (i,o : Nat) -> io (Weights i o)
randomWeights i o = [| MkWeights (randomArr o) (randomMat o i) |]

export
randomWeights' : HasIO io => {i,o:_} -> io (Weights i o)
randomWeights' = [| MkWeights (randomArr o) (randomMat o i) |]

export
randomNet : HasIO io => (i : Nat) -> (hs : List Nat) -> (o : Nat) -> io (Network i hs o)
randomNet i [] o = O <$> randomWeights i o
randomNet i (h :: hs) o = [| L (randomWeights i h) (randomNet h hs o) |]

export
prettyWeights : Weights i o -> String
prettyWeights (MkWeights wBias wNodes) = prettyMatrix wNodes ++ "\n" ++ prettyArray wBias ++ "\n\n"

export
prettyNet : Network i hs o -> String
prettyNet (O x) = prettyWeights x
prettyNet (L x y) = prettyWeights x ++ "\n" ++ prettyNet y

export
runLayer : HasIO io => Weights i o -> SIOArray i Double -> io (SIOArray o Double)
runLayer (MkWeights wB wN) v = wB + !(wN #> v)

export
runNet : HasIO io => Network i hs o -> SIOArray i Double -> io (SIOArray o Double)
runNet (O x) input = mapArray logistic !(runLayer x input)
runNet (L x y) input = do
  z <- runLayer x input
  c <- mapArray logistic z -- this can generalize to other funcs
  runNet y c

export
testRunNet : IO (SIOArray 1 Double)
testRunNet = do
  net <- randomNet 2 [3] 1
  randArr <- randomArr 2
  runNet net randArr

main : IO ()
main = do
  printLn (squares key1 12345)
  printLn (squares2 key1 12345)
