module Net.SSS15M

-- module made to learn how to evolve a 15 minute oracle

import Oanda.ToDB

import Control.Monad.Managed

import Net.FFNN

import Net.Types

import Data.IORef

-- import System.Future

import System.Random
import Net.Random.Squares

import Control.Monad.Random.RandT
import System.Random.PRNG.Squares
import Control.Monad.State

import Data.Strong.IOMatrix
import Data.Strong.IOArray

import Data.List
import Data.Vect

import Util

import TimeIt

-- :exec runStochastic 1 $ record {batch = 4, parentsCount = 15, stochasticity = 0.05, mutRate = 0.1, maxEvaluations = 100, dataSources=100} defaultStochasticEval

fraf' : IO b -> IORef (Maybe b) -> IO (ThreadID, IORef (Maybe b))
fraf' act ref = do
  t <- fork (act >>= writeIORef ref . Just)
  pure (t,ref)



-- use chunksOf to make thread count, or recurse with take untill []
mapConcurrently : (threads : Int) -> (a -> IO b) -> List a -> IO (List b)
mapConcurrently i f xs = do
  futures <- for xs $ \x => newIORef Nothing >>= fraf' (f x)
  Just res <- map sequence . for futures $ \(t,ref) => do
      threadWait t
      readIORef ref
    | Nothing => pure []
  pure res


record StochasticEval where
  constructor MkStochasticEval
  stochasticity : Double
  mutRate : Double
  perturbProb : Double
  parentsCount : Nat
  maxEvaluations : Nat
  randomlyVaryingInitialCondition : Bool
  maxFitness : Double
  batch : Nat -- number of tests to average for fitness
  dataSources : Nat

defaultStochasticEval : StochasticEval
defaultStochasticEval = MkStochasticEval
  0.01 -- stochasticity
  0.05 -- mutRate
  0.5 -- perturbProb    -- half chance of mut half of perturb
  20 -- parentsCount
  500 -- maxEvaluations
  True -- randomlyVaryingInitialCondition
  1 -- maxFitness
  8 -- batch
  20 -- dataSources

average : List Double -> Double
average xs = sum xs / cast (length xs)

sumMoid : HasIO io => DArray o -> io Double
sumMoid arr = sumArray arr

-- evaluate a network and return the squared error
-- we should multiple the array by a coefficient array to bias later guesses
eval' : HasIO io => Network i hs 20 -> (input : DArray i) -> (f : DArray 20 -> io Double) -> (target : DArray 20) -> io (Double, DArray 20)
eval' net input f target = do
  r <- runNet net input
  -- bias <- fromList [1.0,1.0,1.0,1.0,2.0,2.0,2.0,2.0,3.0,3.0,3.0,3.0,4.0,4.0,4.0,4.0,5.0,5.0,5.0,5.0]
  diff <- zipWithArray (-) target r
  -- err <- f !(zipWithArray (*) diff bias)
  err <- sumArray =<< mapArray squared diff
  errs <- toList =<< mapArray (\x => 1 - squared x) diff
  let fitness = 1 - err
  let fitness' = average errs
  pure (fitness', r)

eval : HasIO io => Network i hs o -> (input : DArray i) -> (f : DArray o -> io Double) -> (target : Double) -> io (Double,Double)
eval net input f target = do
  r <- runNet' leakyRelu net input
  res <- f r
  let err = target - res
      fitness = 1 - squared err
  pure (fitness, res)

export
randomArr : HasIO io => MonadState (Bits64,Bits64) io => {s : _} -> io (DArray s)
randomArr = newArrayFillM _ (\_ => randomWeight)

export
randomMat : HasIO io => MonadState (Bits64,Bits64) io => {m,n : _} -> io (SIOMatrix m n Double)
randomMat = newFillM (cast m) (cast n) (\_,_ => randomWeight)

export
randomWeights : HasIO io => MonadState (Bits64,Bits64) io => {i,o : _} -> io (Weights i o)
randomWeights = [| MkWeights randomArr randomMat |]

-- It was found that initializing weights, or bias, or both, to 1 instead of
-- random was not beneficial.
export
randomNet : HasIO io => MonadState (Bits64,Bits64) io => {i,hs,o : _} -> io (Network i hs o)
randomNet {hs = []} = O <$> randomWeights
randomNet {hs = _ :: _} = [| L randomWeights randomNet |]

copyWeights : HasIO io => Weights i o -> io (Weights i o)
copyWeights w = [| MkWeights (mapArray id (wBias w)) (imapMatrixM (\_,_,x => pure x) (wNodes w)) |]

copyNet : HasIO io => Network i hs o -> io (Network i hs o)
copyNet (O w) = [| O (copyWeights w) |]
copyNet (L w y) = [| L (copyWeights w) (copyNet y) |]

-- 100 input bars of open,high,low,close. 5 ouputs, the predictions of the coming candles
-- I might need relu/swish here to allow for larger values
export
randParent : HasIO io => MonadState (Bits64,Bits64) io => io (Network 400 [200,100,40] 20)
-- randParent : HasIO io => MonadState (Bits64,Bits64) io => io (Network 400 [100,200,120,80] 20)
randParent = randomNet

export
mutate : MonadState (Bits64,Bits64) m => (mutProb : Double) -> (perturbProb : Double) -> Double -> m Double
mutate mutProb perturbProb v = do
  if !randomNormalP <= mutProb
    then if !randomNormalP <= perturbProb
           then perturbWeight v
           else randomWeight
    else pure v

-- perturbProb is the prob that a mutation, if it occurs, is a perturbation
mutateWeights : HasIO io => MonadState (Bits64,Bits64) io => (mutProb : Double) -> (perturbProb : Double) -> Weights i o -> io (Weights i o)
mutateWeights mutProb perturbProb (MkWeights wBias wNodes) =
    let mut = mutate mutProb perturbProb
    in [| MkWeights (imapArrayM (\_,v => mut v) wBias) (imapMatrixM (\_,_,v => mut v) wNodes) |]

mutateNet : HasIO io => MonadState (Bits64,Bits64) io => (mutProb : Double) -> (perturbProb : Double) -> Network i hs o -> io (Network i hs o)
mutateNet mutProb perturbProb net = go net
  where
    go : forall i,hs,o. Network i hs o -> io (Network i hs o)
    go (O w) = O <$> mutateWeights mutProb perturbProb w
    go (L w l) = [| L (mutateWeights mutProb perturbProb w) (go l) |]

-- (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))
stochasticFitness : HasIO m => MonadState (Bits64,Bits64) m => StochasticEval -> Double -> m Double
stochasticFitness params fitness = do
  let range = stochasticity params * maxFitness params
  w <- randomNormalR (-range,range)
  pure $ fitness * (1 + w)

randBit : MonadState (Bits64,Bits64) io => io Double
randBit = pure $ if !nextRand > 0 then 1.0 else 0.0

-- get data is slow slow slow
getData : HasIO io => MonadState (Bits64,Bits64) io => io (Maybe (DArray 400, DArray 20))
getData = timeIt "getData" $ do
    -- start <- show <$> nextRandRW (0,280000)  -- random number roughly between 0 and db size - 100
    start <- show . (`mod`280000) <$> nextRandW -- random number roughly between 0 and db size - 100
    -- liftIO $ putStrLn start
    let count = "105" -- we want 5 extra as targets
        sql = "where granularity = \"M15\" and instrument = \"USD_CAD\" order by opentime limit \{start},\{count}"
    -- liftIO $ putStrLn sql
    input' <- liftIO $ getCandles'' sql
    let (inputs,targets) = splitAt 100 input'
        inputs'  = cast {to=Double} <$> concatMap sqlCandleMids inputs
        targets' = cast {to=Double} <$> concatMap sqlCandleMids targets
    (is ** input)  <- fromList' inputs'
    (ts ** target) <- fromList' targets'
    -- putStrLn $ prettyArray input
    -- putStrLn $ prettyArray target
    case is of
      400 => case ts of -- eval pop
               20 => pure $ Just (input,target)
               _  => pure Nothing
      _ => pure Nothing

randomRead : HasIO io => MonadState (Bits64,Bits64) io => SIOArray s a -> io a
randomRead arr = do
  let c = cast $ !nextRandW `mod` cast (size arr)
  unsafeReadArray arr c

-- I should be doing the random input choices here, grab 8 and try each out per net.
evalParent : HasIO io => MonadState (Bits64,Bits64) io => StochasticEval -> SIOArray s (DArray 400, DArray 20) -> Genome 400 20 -> io (Genome 400 20, Genome 400 20)
evalParent params datas' p@(MkGenome parentNet parentFit) = do
    datas <- replicateA (batch params) (randomRead datas')

    -- copy parent and mutate
    childNet <- copyNet parentNet >>= mutateNet (mutRate params) (perturbProb params)

    -- re-eval parent
    ps <- traverse (\(inp,tar) => fst <$> eval' parentNet inp sumMoid tar) datas
    -- eval copy
    cs <- traverse (\(inp,tar) => fst <$> eval' childNet inp sumMoid tar) datas

    -- average fitnesses and apply stochasticity to improve exploration
    sfp <- stochasticFitness params (average ps)
    sfc <- stochasticFitness params (average cs)
    pure (MkGenome parentNet sfp, MkGenome childNet sfc)

fraf : IORef (Maybe (Genome 400 20, Genome 400 20)) -> StateT (Bits64,Bits64) IO (Genome 400 20, Genome 400 20) -> IO ()
fraf ref st = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  res <- evalStateT (seed1,seed2) st
  writeIORef ref (Just res)

-- basetime 2010-01-01T00.000000000Z
-- randomTime : HasIO io => MonadState (Bits64,Bits64) io => io DateTime

pLoop : StochasticEval -> (parents : List (Genome 400 20)) -> SIOArray s (DArray 400, DArray 20) -> StateT (Bits64,Bits64) IO (List (Genome 400 20))
pLoop params parents datas = timeIt "pLoop" $ do
    evts <- liftIO $ for parents $ \p => do
      ref <- newIORef Nothing
      t <- fork (fraf ref (evalParent params datas p))
      pure (t,ref)
        -- evs consists of evaluated parent and child
        -- unzip them, concat, sort by fitness, and take (parentsCount params)
    Just evs <- liftIO $ map sequence $ for evts (\(t,ref) => threadWait t *> readIORef ref)
      | Nothing => putStrLn "evs failure" *> pure []
    let (pNets,cNets) = unzip evs
        nets = pNets ++ cNets
        sortedNets = sortOn @{Down} fitness nets -- sort best first
        finalNets = take (parentsCount params) sortedNets
    printLn $ map fitness finalNets
    pure finalNets

popLoop : StochasticEval -> (parents : List (Genome 400 20)) -> SIOArray s (DArray 400, DArray 20) -> Nat -> StateT (Bits64,Bits64) IO (List (Genome 400 20))
popLoop params parents datas Z = pure parents
popLoop params parents datas (S k) = popLoop params !(pLoop params parents datas) datas k

-- I need to learn how to save nets now so I can work on them whenever

export
stochasticXor : StochasticEval -> StateT (Bits64,Bits64) IO Double
stochasticXor params = do
    -- preget a bunch of trial data here and pass it along, getting trial data
    -- during evaluation is wicked expensive
    -- make an array of data and just pick batchNo of indexes at random

    Just datas <- timeIt "main:get all datas" $ sequence <$> replicateA (dataSources params) getData
      | _ => putStrLn "data generation error" *> pure 0
    (s ** training_data) <- fromList' datas

    -- at some point I want to pull some bests-of from sql and use them as the starting pop
    parents <- replicateA (parentsCount params) (pure (MkGenome !randParent 0.0))
    -- traverse_ (\(MkGenome n _) => putStrLn (prettyNet n)) parents
    -- evolve parents for max evaluations
    bests <- popLoop params parents training_data (maxEvaluations params)
    putStrLn "Bests:"
    printLn (map fitness bests)
    (MkGenome bestNet f) :: _ <- pure bests
      | _ => pure 0
    putStrLn "Best fitness:"
    printLn f

    -- gen some data and try it
    Just (inp,tar) <- getData
      | _ => pure f
    (fit,res) <- eval' bestNet inp sumMoid tar
    putStrLn "Target:"
    putStrLn $ prettyArray tar
    putStrLn "Result:"
    putStrLn $ prettyArray res
    putStrLn "Fitness:"
    printLn fit

    pure f



{-

The Stochastic Steady State (SSSXOR) is a (μ + μ) evolutionary strategy [49] that
operates on the basis of populations formed by μ parents. During each generation
each parent generates one offspring, the parent and the offspring are evaluated,
and the best μ individuals are selected as new parents (see the pseudo-code
below). It is a method developed by us that belongs to the class of methods
proposed by [14–15]. The novelty with respect to previous related methods
consists in the introduction of the Stochasticity parameter that permits to
regulate the selective pressure. This is obtained by adding to the fitness of
individuals a value randomly selected in the range [-Stochasticity*MaxFitness,
Stochasticity*MaxFitness] with a uniform distribution. When this parameter is
set to 0.0 only the best μ individuals are allowed to reproduce. The higher the
value of the parameter is, the higher the probability that other individuals
reproduce is. For a discussion of evolutionary optimization in uncertain
environments and in the presence of a noisy fitness function see [51].

SSSXOR Method:

1: NEvaluations <- 0

  // the genotype of the parents of the first generation in initialized randomly

2: for p <- 0 to NParents do

3:   for g <- 0 to NGenes do

4:     genome[p][g] <- rand(-8.0, 8.0)

5:   Fitness[p] <- evaluate (p)

6:   NEvaluations <- NEvaluations + NTrials

  // evolution is continued until a maximum number of evaluation trials is performed

7: while(NEvaluations < MaxEvaluations) do

8:   for p <- 0 to NParents do

     // in the randomly varying experimental condition parents are re-evaluated

9:    if (RandomlyVaryingInitialCondition) then

10:     Fitness[p] <- evaluate (p)

11:     NEvaluations <- NEvaluations + NTrials

12:    genome[p+NParents] <- genome[p] // create a copy of parents’ genome

13:    mutate-genome(p+NParents) // mutate the genotype of the offspring

14:    Fitness[p+Nparents] <- evaluate[p+NParents]

15:    NEvaluations <- NEvaluations + NTrials

   // noise ensures that parents are replaced by less fit offspring with a low probability

16:      NoiseFitness[p] <- Fitness[p] * (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))

17:    NoiseFitness[p+NParents] <-

         Fitness[p+NParents] * (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))

     // the best among parents and offspring become the new parents

18:  rank genome[NParents*2] for NoiseFitness[NParents*2]

In the experiment reported in this paper the connection weights are evolved and
the topology of the network is kept fixed. The initial population is encoded in
a matrix of μ x θ real numbers that are initialized randomly with a uniform
distribution in the range [-8.0, 8.0], where μ corresponds to the number of
parent and θ corresponds to the total number of weights and biases. Offspring
are generated by creating a copy of the genotype of the parent and by subjecting
each gene to mutation with a MutRate probability. Mutations are realized by
replacing or perturbing a gene value with equal probability. Replacements are
realized by substituting the gene with a new real number randomly generated
within the range [-8.0, 8.0] with a uniform distribution. Perturbations are
realized by adding to the current value of a gene a real number randomly
selected with a Gaussian distribution with a standard deviation of 1.0 and a
mean of 0.0. Values outside the [-8.0, 8.0] range after perturbations are
truncated in the range.
  
This method requires setting two parameters: MutRate and Stochasticity. To
identify the optimal values of the parameters we systematically varied MutRate
in the range [1%, 3%, 5%, 7%, 10%, 15% and 20%] and Stochasticity in the range
[0%, 10%, 20%, 30%, 40%, 50%, 70%, and 100%]. Population size was set to 20. To
enhance the ability of the method to refine the evolved candidate solutions, we
reduced the mutation rate to 1% and we set the Stochasticity to 0% during the
last 1/20 period of the evolutionary process.

-}

-- The thing to watch for is fitness over 1 when it prints the final bests, 1+
-- will get every xor correct.
-- runs and popsize have similar impact on fitness
export
runStochastic : Int -> StochasticEval -> IO ()
runStochastic runs params = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  _ <- runStateT (seed1,seed2) $ do
    r <- for [1 .. runs] (\_ => stochasticXor params)
    pure () -- printLn (sum r)
  pure ()

export
runTest : IO ()
runTest = runStochastic 1 defaultStochasticEval


main : IO ()
main = runStochastic 1 $ record {batch = 4, parentsCount = 15, maxEvaluations = 5} defaultStochasticEval
