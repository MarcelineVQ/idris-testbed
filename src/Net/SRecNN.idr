module Net.SRecNN

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

public export
record RecWeights (o : Nat) where
  constructor MkRecWeights
  wWeights : Array o Double
  wInp : Array o Double

-- public export
-- record SmoothWeights (o : Nat) where
--   constructor MkSmoothWeights
--   -- wBias : Array   o Double
--   wWeights : Array o Double
--   wInp : Array o Double

-- public export
-- record Weights (i : Nat) (o : Nat) where
  -- constructor MkWeights
  -- wBias : Array o Double
  -- wNodes : Matrix o i Double

-- consider chagnign this from  wNodes pre #> wBias pre to an array of weights * wBias pre
-- meaning a node only considers its own history
export
runLayer : Weights i o -> RecWeights o -> Array i Double -> Array o Double
runLayer w pre input =
  let newHidden = wWeights pre * wInp pre
  in mapArray Prelude.tanh $ newHidden + (wNodes w #> input) + wBias w

-- 
-- public export
-- data RecNetwork : Nat -> List Nat -> Nat -> Type where
--   O : Weights i o -> (prev : RecWeights o) -> RecNetwork i [] o
--   L : Activation -> Weights i h -> RecNetwork h hs o -> (prev : RecWeights h) -> RecNetwork i (h :: hs) o
-- 
-- 
-- 
-- -- public export
-- -- data RecNetwork' : (i : Nat) -> (hs : List Nat) -> (o : Nat) -> Type where
--   -- O' : Weights i o -> (prev : RecWeights o) -> RecNetwork' i [] o
--   -- L' : Activation -> Weights i h -> RecNetwork' h hs o -> (prev : RecWeights h) -> RecNetwork' i (h :: hs) o
-- 
-- 
-- 
-- public export
-- record RecGenome (i : Nat) (o : Nat) where
--   constructor MkRecGenome
--   geneNet : RecNetwork i hs o
--   geneFitness : Double
--   geneStochasticFitness : Double
-- 
-- export
-- stepNet : RecNetwork i hs o -> Array i Double -> (RecNetwork i hs o, Array o Double)
-- stepNet (O x prev) input =
--     let r = runLayer x input prev
--         tb = record {wInp = r} prev
--     in (O x tb, r)
-- stepNet (L a x y prev) input =
--     let r = runLayer x input prev
--         c = mapArray (actToFunc a) r
--         tb = record {wInp = c} prev
--         (new,r') = stepNet y c
--     in (L a x new tb, r')
-- 
-- export
-- %inline
-- runNet : (RecNetwork i hs o, Array o Double) -> List (Array i Double) -> Array o Double
-- runNet (n,res) [] = res
-- runNet (n,res) (x :: xs) = runNet (stepNet n x) xs
-- 


-- export
-- testRunNet : IO (Array 1 Double)
-- testRunNet = do
--   net <- randomNet 2 [3] 1
--   randArr <- randomArr 2
--   pure $ runNet net randArr
-- 
-- main : IO ()
-- main = do
--   printLn (squares key1 12345)
--   printLn (squares2 key1 12345)
