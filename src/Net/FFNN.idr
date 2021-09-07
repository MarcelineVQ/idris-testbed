module Net.FFNN

import Net.Random.IO

import Control.Monad.Random.RandT

import Data.Strong.Matrix
import Data.Strong.Array

import System.Random.Natural

import System.Random.PRNG.Squares

import public Net.Activation

import Net.Types

import Data.List

import TimeIt

import Util

-- I want to predict what x bars from now will be, lets say 10 bars
-- most direct choice is feed-forward on 100 bars at once, with
-- high,low,open,close per bar. This means our input layer is 400 wide

export
randomRead : HasIO io => Array s a -> io a
randomRead arr = do
  let c = cast $ !(randomRIO (0, size arr - 1))
  unsafeMutableReadArray arr c

export
randomArr : HasIO io => (s : Nat) -> io (Array s Double)
randomArr s = inewArrayFillM s (\_ => randWeight)

export
randomMat : HasIO io => (m,n : Nat) -> io (Matrix m n Double)
randomMat m n = inewMatrixFillM (cast m) (cast n) (\_,_ => randWeight)

export
randomFun : HasIO io => io Activation
randomFun = randomRead (fromList actList)

export
randomFuns : HasIO io => (s : Nat) -> io (Array s Activation)
randomFuns s = inewArrayFillM s (\_ => randomFun)

export
randomWeights : HasIO io => (i,o : Nat) -> io (Weights i o)
randomWeights i o = [| MkWeights (randomArr o) (randomMat o i) |]

export
randomWeights' : HasIO io => {i,o:_} -> io (Weights i o)
randomWeights' = [| MkWeights (randomArr o) (randomMat o i) |]

export
randomNet : HasIO io => (i : Nat) -> (hs : List Nat) -> (o : Nat) -> io (Network i hs o)
randomNet i [] o = O <$> randomWeights i o
randomNet i (h :: hs) o = [| L randomFun (randomWeights i h) (randomNet h hs o) |]

ploos : Double -> Double
ploos = sigmoid

export
runLayer : Weights i o -> Array i Double -> Array o Double
runLayer w v = wBias w + wNodes w #> v

export
runNet' : Network i hs o -> Array i Double -> Array o Double
-- runNet' (O x) input = mapArray (actToFunc Relu) $ runLayer x input
runNet' (O x) input = runLayer x input
runNet' (L a x y) input =
  let r = runLayer x input
      c = mapArray (actToFunc a) r
      r' = runNet' y c
  in r'

export
%inline
runNet : Network i hs o -> Array i Double -> Array o Double
runNet n inp = runNet' n inp

export
testRunNet : IO (Array 1 Double)
testRunNet = do
  net <- randomNet 2 [3] 1
  randArr <- randomArr 2
  pure $ runNet net randArr

main : IO ()
main = do
  printLn (squares key1 12345)
  printLn (squares2 key1 12345)
