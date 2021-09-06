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
randomFuns : HasIO io => (s : Nat) -> io (SIOArray s Activation)
randomFuns s = do
  funs <- fromList actList
  newArrayFillM s (\_ => randomRead funs)

export
randomWeights : HasIO io => (i,o : Nat) -> io (Weights i o)
randomWeights i o = [| MkWeights (randomFuns o) (randomArr o) (randomMat o i) |]

export
randomWeights' : HasIO io => {i,o:_} -> io (Weights i o)
randomWeights' = [| MkWeights (randomFuns o) (randomArr o) (randomMat o i) |]

export
randomNet : HasIO io => (i : Nat) -> (hs : List Nat) -> (o : Nat) -> io (Network i hs o)
randomNet i [] o = O <$> randomWeights i o
randomNet i (h :: hs) o = [| L (randomWeights i h) (randomNet h hs o) |]

ploos : Double -> Double
ploos = sigmoid

export
runLayer : HasIO io => Weights i o -> SIOArray i Double -> io (SIOArray o Double)
runLayer w@(MkWeights funs wB wN) v = do
    -- putStr "inp: " *> printLn v
    -- putStr "weights: " *> putStrLn (prettyWeights w)
    mat <- wN #> v
    -- putStr "mat: " *> printLn mat
    plus <- wB + mat
    -- putStr "plus: " *> printLn plus
    funs' <- mapArray actToFunc funs
    -- putStr "mapArray: " *> printLn funs'
    r <- zipWithArray (\f,x => f x) funs' plus
    -- putStr "zipWithArray: " *> printLn r
    pure r
-- ^ this is taking my weights and spitting them out

export
runLayer'' : HasIO io => Weights i o -> SIOArray i Double -> io (SIOArray o Double)
runLayer'' (MkWeights funs wB wN) v = wB + !(wN #> v)

-- export
-- runLayer' : Weights i o -> SIOArray i Double -> SIOArray o Double
-- runLayer' (MkWeights funs wB wN) v = wB + (wN ##> v)

export
runNet' : HasIO io => (Double -> Double) -> Network i hs o -> SIOArray i Double -> io (SIOArray o Double)
runNet' f (O x) input = do
  r <- runLayer'' x input
  -- putStr "runNet O: " *> printLn r
  pure r
runNet' f (L x y) input = do

  z <- runLayer x input
  -- putStr "runLayer S: " *> printLn z
  c <- mapArray f z -- runLayer applies the relevant func
  -- putStr "mapArray S: " *> printLn c
  r <- runNet' f y z
  -- putStr "runNet S: " *> printLn r
  pure r
  -- runNet' f y out

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
