module Net.FFNN

import Net.Random.IO

import Control.Monad.Random.RandT

import Data.Strong.IOMatrix
import Data.Strong.IOArray

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
randomRead : HasIO io => SIOArray s a -> io a
randomRead arr = do
  let c = cast $ !(randomRIO (0, size arr - 1))
  unsafeReadArray' arr c

export
randomArr : HasIO io => (s : Nat) -> io (SIOArray s Double)
randomArr s = newArrayFillM s (\_ => randWeight)

export
randomMat : HasIO io => (m,n : Nat) -> io (SIOMatrix m n Double)
randomMat m n = newFillM (cast m) (cast n) (\_,_ => randWeight)

export
randomFun : HasIO io => io Activation
randomFun = do
  funs <- fromList actList
  randomRead funs

export
randomFuns : HasIO io => (s : Nat) -> io (SIOArray s Activation)
randomFuns s = do
  funs <- fromList actList
  newArrayFillM s (\_ => randomRead funs)

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
runLayer : HasIO io => Weights i o -> SIOArray i Double -> io (SIOArray o Double)
runLayer w v = do
    mat <- {- timeIt "array mult" $ -} (wNodes w) #> v
    plus <- {- timeIt "array plus" $ -} (wBias w) + mat
    pure plus
-- -- ^ this is taking my weights and spitting them out

export
runNet' : HasIO io => Network i hs o -> SIOArray i Double -> io (SIOArray o Double)
runNet' (O x) input = runLayer x input
runNet' (L a x y) input = do
  r <- runLayer x input
  c <- mapArray (actToFunc a) r
  r <- runNet' y c
  pure r

export
%inline
runNet : HasIO io => Network i hs o -> SIOArray i Double -> io (SIOArray o Double)
runNet n inp = do
  r <- runNet' n inp
  -- putStr "runNet final: " *> printLn r
  pure r

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
