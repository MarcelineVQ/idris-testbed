module Net.FFNN

import Net.Random.IO

import Control.Monad.Random.RandT

import Data.IOMatrix

import Data.Strong.IOMatrix
import Data.Strong.IOArray

import System.Random.Natural

import System.Random.PRNG.Squares

import public Net.Activations

import Net.Types

import Util

-- I want to predict what x bars from now will be, lets say 10 bars
-- most direct choice is feed-forward on 100 bars at once, with
-- high,low,open,close per bar. This means our input layer is 400 wide

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
runLayer : HasIO io => Weights i o -> SIOArray i Double -> io (SIOArray o Double)
runLayer (MkWeights wB wN) v = wB + !(wN #> v)

export
runNet' : HasIO io => (Double -> Double) -> Network i hs o -> SIOArray i Double -> io (SIOArray o Double)
runNet' f (O x) input = runLayer x input -- mapArray f !(runLayer x input) -- don't run on last layer, if we want to clamp the layer, do it when evaluating
runNet' f (L x y) input = do
  z <- runLayer x input
  c <- mapArray f z
  runNet' f y c

export
%inline
runNet : HasIO io => Network i hs o -> SIOArray i Double -> io (SIOArray o Double)
runNet = runNet' logistic

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
