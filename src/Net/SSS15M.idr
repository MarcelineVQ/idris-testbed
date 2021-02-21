module Net.SSS15M

-- module made to learn how to evolve a 15 minute oracle

import Oanda.ToDB

import Control.Monad.Managed

import Net.FFNN

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

defaultStochasticEval : StochasticEval
defaultStochasticEval = MkStochasticEval
  0.05 -- mut chance
  0.01 -- stochastic fitness modification
  0.5 -- half chance of mut half of perturb
  20
  500
  True
  1
  1

-- SIOArray of Doubles
public export
DArray : Nat -> Type
DArray n = SIOArray n Double

sumMoid : HasIO io => DArray o -> io Double
sumMoid arr = sumArray arr

-- evaluate a network and return the squared error
eval' : HasIO io => Network i hs o -> (input : DArray i) -> (f : DArray o -> io Double) -> (target : DArray o) -> io (Double, DArray o)
eval' net input f target = do
  r <- runNet net input
  err <- f !(zipWithArray (-) target r)
  let fitness = 1 - squared err
  pure (fitness, r)

eval : HasIO io => Network i hs o -> (input : DArray i) -> (f : DArray o -> io Double) -> (target : Double) -> io (Double,Double)
eval net input f target = do
  r <- runNet net input
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

export
data Genome : Nat -> Type where
  MkGenome : Network i hs o -> (fitness : Double) -> Genome i

export
fitness : Genome i -> Double
fitness (MkGenome _ f) = f

-- 100 input bars of open,high,low,close. 5 ouputs, the predictions of the coming candles
-- I might need relu/swish here to allow for larger values
export
randParent : HasIO io => MonadState (Bits64,Bits64) io => io (Network 400 [100,50,25,10] 5)
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

average : List Double -> Double
average xs = sum xs / cast (length xs)

prettyGenome : Genome i -> String
prettyGenome (MkGenome net f) = "MkGenome " ++ prettyNet net ++ " " ++ show f

getData : HasIO io => MonadState (Bits64,Bits64) io => io (Maybe (DArray 400, DArray 5))
getData = do
    start <- show <$> nextRandRW (0,280000)  -- random number roughly between 0 and db size - 100
    liftIO $ putStrLn start
    let count = "105" -- we want 5 extra as targets
        sql = "where granularity = \"M15\" and instrument = \"USD_CAD\" order by opentime limit \{start},\{count}"
    liftIO $ putStrLn sql
    input' <- liftIO $ getCandles'' sql
    let (inputs,targets) = splitAt 100 input'
        inputs = cast {to=Double} <$> concatMap sqlCandleMids inputs
    (is ** input) <- liftIO $ fromList' inputs
    (ts ** target) <- liftIO $ fromList' targets
    case is of
      400 => case ts of -- eval pop
        5 => ?dsfdssd --pure $ Just (input,target)
        _ => pure Nothing
      _ => pure Nothing

-- I should be doing the random input choices here, grab 8 and try each out per net.
evalParent : HasIO io => MonadState (Bits64,Bits64) io => StochasticEval -> Genome 400 -> io (Genome 400, Genome 400)
evalParent params p@(MkGenome parentNet parentFit) = do
    Just datas <- sequence <$> replicateA 8 getData
      | _ => putStrLn "data generation error" *> pure (p,p)

    -- re-eval parent
    (zs,rs) <- unzip <$> traverse (\(inp,tar) => eval' parentNet inp sumMoid ?dsfsdf) datas
    
    ?sdffsdfsd

    -- copy parent and mutate
    -- childNet <- copyNet parentNet >>= mutateNet (mutRate params) (perturbProb params)
    -- eval copy
    -- (zs',rs') <- unzip <$> traverse (\inp => eval childNet input sumMoid target) input
    -- let res' = average zs'
    -- pure (MkGenome parentNet !(stochasticFitness params parentFit), MkGenome childNet !(stochasticFitness params res'))

-- basetime 2010-01-01T00.000000000Z
-- randomTime : HasIO io => MonadState (Bits64,Bits64) io => io DateTime

pLoop : StochasticEval -> (parents : List (Genome 400)) -> StateT (Bits64,Bits64) IO (List (Genome 400))
pLoop params parents = do
    -- get our input data
    start <- show <$> nextRandRW (0,280000)  -- random number roughly between 0 and db size - 100
    liftIO $ putStrLn start
    let count = "105" -- we want 5 extra as targets
        sql = "where granularity = \"M15\" and instrument = \"USD_CAD\" order by opentime limit \{start},\{count}"
    liftIO $ putStrLn sql
    input' <- liftIO $ getCandles'' sql
    let (inputs,targets) = splitAt 100 input'
        inputs = cast {to=Double} <$> concatMap sqlCandleMids inputs
    (is ** input) <- liftIO $ fromList' inputs
    (ts ** target) <- liftIO $ fromList' targets
    evs <- case is of
          400 => case ts of -- eval pop
            5 => for parents $ \p => evalParent params p
            _ => pure []
          _ => pure []
        -- evs consists of evaluated parent and child
        -- unzip them, concat, sort by fitness, and take (parentsCount params)
    let (pNets,cNets) = unzip evs
        nets = pNets ++ cNets
        sortedNets = sortOn @{Down} fitness nets -- sort best first
        finalNets = take (parentsCount params) sortedNets
    pure finalNets

popLoop : StochasticEval -> (parents : List (Genome 400)) -> Nat -> StateT (Bits64,Bits64) IO (List (Genome 400))
popLoop params parents Z = pLoop params parents
popLoop params parents (S k) = popLoop params !(pLoop params parents) k

export
stochasticXor : StochasticEval -> StateT (Bits64,Bits64) IO Double
stochasticXor params = do
    parents <- replicateA (parentsCount params) (pure (MkGenome !randParent 0.0))
    -- traverse_ (\(MkGenome n _) => putStrLn (prettyNet n)) parents
    -- evolve parents for max evaluations
    bests <- popLoop params parents (maxEvaluations params)
    printLn (map fitness bests)
    (MkGenome bestNet f) :: _ <- pure bests
      | _ => pure 0
    printLn f
    -- best
    -- input <- newArray 2 0.0
    -- x <- pure 1
    -- y <- pure 1
    -- writeArray input 0 x  
    -- writeArray input 1 y
    -- putStr $ prettyArray input
    -- putStrLn $ ": target " ++ show (xorTarget x y)
    -- (err,res) <- eval bestNet input sumMoid (xorTarget x y)
    -- printLn (err,res,xorFit res)
    -- 
    -- x <- pure 0
    -- y <- pure 0
    -- writeArray input 0 x
    -- writeArray input 1 y
    -- putStr $ prettyArray input
    -- putStrLn $ ": target " ++ show (xorTarget x y)
    -- (err,res) <- eval bestNet input sumMoid (xorTarget x y)
    -- printLn (err,res,xorFit res)
    -- 
    -- x <- pure 1
    -- y <- pure 0
    -- writeArray input 0 x
    -- writeArray input 1 y
    -- putStr $ prettyArray input
    -- putStrLn $ ": target " ++ show (xorTarget x y)
    -- (err,res) <- eval bestNet input sumMoid (xorTarget x y)
    -- printLn (err,res,xorFit res)
    -- 
    -- x <- pure 0
    -- y <- pure 1
    -- writeArray input 0 x
    -- writeArray input 1 y
    -- putStr $ prettyArray input
    -- putStrLn $ ": target " ++ show (xorTarget x y)
    -- (err,res) <- eval bestNet input sumMoid (xorTarget x y)
    -- printLn (err,res,xorFit res)
    
    -- putStrLn $ prettyNet bestNet
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
runStochastic : StochasticEval -> IO ()
runStochastic params = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  _ <- runStateT (seed1,seed2) $ do
    r <- for [1..20] (\_ => stochasticXor params)
    printLn (sum r)
  pure ()

export
runTest : IO ()
runTest = runStochastic defaultStochasticEval


main : IO ()
main = runStochastic defaultStochasticEval
