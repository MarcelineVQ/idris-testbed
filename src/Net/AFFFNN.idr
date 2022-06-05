module Net.AFFFNN

import Net.Random.IO

import Control.Monad.Random.RandT

import Data.Strong.Matrix
import Data.Strong.Array

import System.Random

import System.Random.Natural

import System.Random.PRNG.Squares

import public Net.Activation

import Data.ArrayFire

-- import Net.Types

import System.Random.Types

import Data.List

import TimeIt

import Util

import JSON
import Generics.Derive
%language ElabReflection

public export
Mat : (i : Nat) -> (o : Nat) -> Type
Mat i o = AFArray [i,o] F64

public export
Arr : (i : Nat) -> Type
Arr i = AFArray [i] F64

public export
record Weights (i : Nat) (o : Nat) where
  constructor MkWeights
  wBias : Arr o
  wNodes : Mat o i
%runElab derive "Weights" [Generic,Meta]

{-
Now, a Weights linking an m-node layer to an n-node layer has an n-dimensional
bias vector (one component for each output) and an n-by-m node weight matrix
(one column for each output, one row for each input).
-}
public export
data Network : Nat -> List Nat -> Nat -> Type where
  O : Weights i o -> Network i [] o
  L : {h:_} -> Weights i h -> Network h hs o -> Network i (h :: hs) o

public export
record Genome (i : Nat) (o : Nat) where
  constructor MkGenome
  geneNet : Network i hs o
  geneFitness : Double
  geneStochasticFitness : Double

export
randomArr : (eng : RandomEngine) => (s : Nat) -> Arr s
randomArr s = randomUniform eng F64 [s]

export
randomWeights : (eng : RandomEngine) => {i,o:_} -> Weights i o
-- randomWeights = MkWeights (randomUniform'' * 0.01) randomUniform'' -- randomArr' randomMat'
-- randomWeights = MkWeights (0.01) (randomUniform'' * 0.01) -- randomArr' randomMat'
randomWeights = MkWeights 0 (randomUniform'' * 0.01)

-- ninja trader
-- chart automated strategey called brackets

export
randomNet : RandomEngine => (i : Nat) -> (hs : List Nat) -> (o : Nat) -> Network i hs o
randomNet i [] o = O randomWeights
randomNet i (h :: hs) o = L randomWeights (randomNet h hs o)

size : {s:_} -> Arr s -> Nat
size _ = s

export
runLayer : {o:_} -> Weights i o -> AFArray [i] F64 -> AFArray [o] F64
runLayer w v = wBias w + wNodes w #> v

relu : {i:_} -> Arr i -> Arr i
relu = max 0

leakyRelu : {i:_} -> Arr i -> Arr i
-- leakyRelu arr = select (arr `le` 0) (arr * 0.01) arr
leakyRelu arr = max (arr * 0.01) arr -- quite a bit faster, select is slow

expRelu : {i:_} -> Arr i -> Arr i
expRelu arr = max (expM1 arr) arr


softMax : {i:_} -> Arr i -> Arr i
softMax arr = let r = sigmoid arr
                  s = sumAll r
              in r / fromDouble s

export
runNet : RandomEngine => {i,o:_} -> Network i hs o -> Arr i -> Arr o
runNet (O x) input = runLayer x input
runNet (L x y) input =
  let r = runLayer x input
      -- c = ArrayFire.sigmoid r
      c = leakyRelu r
      r' = runNet y c
  in r'

export
testRunNet : RandomEngine => Arr 3
testRunNet =
  let net = randomNet 2000 [323,323,323,323,323,323,323,323,323,323,323] 3
      randArr = randomArr 2000
  in runNet net randArr

export
main : IO ()
main = do
  seed <- cast {from=Int} {to=Bits64} <$> randomIO
  -- _ <- afSetSeed seed --12345
  Right eng <- afCreateRandomEngine AF_RANDOM_ENGINE_DEFAULT seed
    | Left err => printLn err
  Right str <- afArrayToString testRunNet
    | Left err => printLn err
  putStrLn str
  Right str <- afArrayToString testRunNet
    | Left err => printLn err
  putStrLn str
  Right str <- afArrayToString testRunNet
    | Left err => printLn err
  putStrLn str
  Right str <- afArrayToString testRunNet
    | Left err => printLn err
  putStrLn str