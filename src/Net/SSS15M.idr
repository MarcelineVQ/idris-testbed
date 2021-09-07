module Net.SSS15M

-- module made to learn how to evolve a 15 minute oracle

import Oanda.ToDB

import Decidable.Equality

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

import Data.Strong.Matrix
import Data.Strong.Array

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
  funcMutRate : Double
  perturbProb : Double
  parentsCount : Nat
  maxEvaluations : Nat
  refiningEvaluations : Nat
  randomlyVaryingInitialCondition : Bool
  maxFitness : Double
  batch : Nat -- number of tests to average for fitness
  dataSources : Nat

defaultStochasticEval : StochasticEval
defaultStochasticEval = MkStochasticEval
  0.01 -- stochasticity
  0.05 -- mutRate
  0.005 -- funcMutRate
  0.5 -- perturbProb    -- half chance of mut half of perturb
  20 -- parentsCount
  400 -- maxEvaluations
  100 -- refiningEvaluations
  True -- randomlyVaryingInitialCondition
  1 -- maxFitness
  8 -- batch
  20 -- dataSources

multiplier : Double
multiplier = 100000

-- in and out must be multiples of 4
%tcinline
InSize : Nat
InSize = 400

%tcinline
OutSize : Nat
OutSize = 4

NetShape : Type
-- NetShape = Network InSize (replicate 40 12) OutSize
-- NetShape = Network InSize ([20,100,100,100,20,12,8]) OutSize 
NetShape = Network InSize (replicate 10 50 ++ replicate 10 20) OutSize
  
average : List Double -> Double
average xs = sum xs / cast (length xs)

sumMoid : HasIO io => DArray o -> io Double
sumMoid arr = pure $ sumArray arr

%inline
minDouble : Double
minDouble = -1.797e308


export
minimum : List Double -> Double
minimum = foldr min 1.797e308

-- evaluate a network and return the squared error
-- we could multiple the array by a coefficient array to bias later guesses
-- 1 might be a bad basis, USD_CAD isn't far from it in the first place
eval' : HasIO io => Network i hs o -> (input : DArray i) -> (f : DArray o -> io Double) -> (target : DArray o) -> io (Double, DArray o)
eval' net input f target = do
  let r = runNet net input
      diff = zipWithArray (-) target r
      errs = toList $ mapArray (\x => 1 - squared x) diff
      fitness'' =  minimum errs -- choose the worstestsest, to promote all answers being right
  pure (fitness'', r)

randomRead : HasIO io => MonadState (Bits64,Bits64) io => Array s a -> io a
randomRead arr = do
  let c = cast $ !nextRandW `mod` cast (size arr)
  unsafeMutableReadArray arr c

randomRead' : HasIO io => MonadState (Bits64,Bits64) io => Array s a -> io (Nat,a)
randomRead' arr = do
  let c = cast $ !nextRandW `mod` cast (size arr)
  pure $ (c,!(unsafeMutableReadArray arr c))

randomFun : HasIO io => MonadState (Bits64,Bits64) io => io Activation
randomFun = SSS15M.randomRead (fromList actList)

randomFuns : HasIO io => MonadState (Bits64,Bits64) io => {s : _} -> io (Array s Activation)
randomFuns = inewArrayFillM s (\_ => SSS15M.randomFun)

export
randomArr : HasIO io => MonadState (Bits64,Bits64) io => {s : _} -> io (DArray s)
randomArr = inewArrayFillM _ (\_ => randomWeight)

export
randomMat : HasIO io => MonadState (Bits64,Bits64) io => {m,n : _} -> io (Matrix m n Double)
randomMat = inewMatrixFillM (cast m) (cast n) (\_,_ => randomWeight)

export
randomWeights : HasIO io => MonadState (Bits64,Bits64) io => {i,o : _} -> io (Weights i o)
randomWeights = [| MkWeights randomArr randomMat |]

export
neutralWeights : HasIO io => MonadState (Bits64,Bits64) io => {i,o : _} -> io (Weights i o)
neutralWeights = [| MkWeights (inewArrayFillM _ (\_ => pure 1.0)) randomMat |]

export
randomNet : HasIO io => MonadState (Bits64,Bits64) io => {i,hs,o : _} -> io (Network i hs o)
randomNet {hs = []} = [| O randomWeights |]
randomNet {hs = _ :: _} = [| L SSS15M.randomFun randomWeights randomNet |]

copyWeights : Weights i o -> Weights i o
copyWeights w = MkWeights (newArrayCopy (wBias w)) (newMatrixCopy (wNodes w))

copyNet : Network i hs o -> Network i hs o
copyNet (O w) = O (copyWeights w)
copyNet (L a w y) = L a (copyWeights w) (copyNet y)

-- 100 input bars of open,high,low,close. 5 ouputs, the predictions of the coming candles
-- I might need relu/swish here to allow for larger values
export
-- randParent : HasIO io => MonadState (Bits64,Bits64) io => io (Network 400 [200,100,40] 4)
-- randParent : HasIO io => MonadState (Bits64,Bits64) io => io (Network 400 [20,20,20,20,20,20] 4)
-- randParent : HasIO io => MonadState (Bits64,Bits64) io => io (Network 400 (replicate 8 20) 4)
randParent : HasIO io => MonadState (Bits64,Bits64) io => io (NetShape)
randParent = randomNet

export
mutate : MonadState (Bits64,Bits64) m => (mutProb : Double) -> (perturbProb : Double) -> Double -> m Double
mutate mutProb perturbProb v = do
  if !randomNormalP <= mutProb
    then if !randomNormalP <= perturbProb
           then perturbWeight v
           else randomWeight
    else pure v

mutFuns : HasIO m => MonadState (Bits64,Bits64) m => (mutProb : Double) -> Activation -> m Activation
mutFuns mutProb f = do
  if !randomNormalP <= mutProb
    then SSS15M.randomFun
    else pure f

-- perturbProb is the prob that a mutation, if it occurs, is a perturbation
mutateWeights : HasIO io => MonadState (Bits64,Bits64) io => (mutProb : Double) -> (perturbProb : Double) -> Weights i o -> io (Weights i o)
mutateWeights mutProb perturbProb (MkWeights wBias wNodes) =
    let mut = mutate mutProb perturbProb
    in [| MkWeights (imapArrayM (\_,v => mut v) wBias) (imapMatrixM (\_,_,v => mut v) wNodes) |]

mutateNet : HasIO io => MonadState (Bits64,Bits64) io => StochasticEval -> Network i hs o -> io (Network i hs o)
mutateNet params net = go net
  where
    go : forall i,hs,o. Network i hs o -> io (Network i hs o)
    go (O w) = O <$> mutateWeights (mutRate params) (perturbProb params) w
    go (L a w l) = [| L (mutFuns (funcMutRate params) a) (mutateWeights (mutRate params) (perturbProb params) w) (go l) |]

-- (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))
stochasticFitness : HasIO m => MonadState (Bits64,Bits64) m => StochasticEval -> Double -> m Double
stochasticFitness params fitness = do
  let range = stochasticity params * maxFitness params
  w <- randomNormalR (-range,range)
  let f = fitness * (1 + w)
  -- when (f > 1.0) (printLn w)
  pure f

randBit : MonadState (Bits64,Bits64) io => io Double
randBit = pure $ if !nextRand > 0 then 1.0 else 0.0

-- get data is slow slow slow
getData : HasIO io => MonadState (Bits64,Bits64) io => {i,o : _} -> io (Maybe (DArray i, DArray o))
getData = timeIt "getData" $ do
    -- start <- show <$> nextRandRW (0,280000)  -- random number roughly between 0 and db size - 100
    -- start <- show . (`mod`280000) <$> nextRandW -- random number roughly between 0 and db size - 100
    start <- show . (`mod`3313) <$> nextRandW -- random number roughly between 0 and db size - 100
    -- liftIO $ putStrLn start
    let z = cast {to=Int} i `div` 4
    let count = show (z + 1) -- "101" -- we want 5 extra as targets
        sql = "where granularity = \"H1\" and instrument = \"USD_CAD\" order by opentime limit \{start},\{count}"
    -- putStrLn sql
    input' <- liftIO $ getCandles'' sql
    let (inputs,targets) = splitAt (cast z) input'
        inputs'  = (* multiplier) . cast {to=Double} <$> concatMap sqlCandleMids inputs
        targets' = (* multiplier) . cast {to=Double} <$> concatMap sqlCandleMids targets
        (is ** input)  = fromList' inputs'
        (ts ** target) = fromList' targets'
    -- printLn input
    -- printLn target
    case (decEq is i, decEq ts o) of
      (Yes Refl, Yes Refl) => pure $ Just (input,target)
      _ => pure Nothing

-- I should be doing the random input choices here, grab 8 and try each out per net.
evalParent : HasIO io => MonadState (Bits64,Bits64) io => StochasticEval -> Array s (DArray InSize, DArray OutSize) -> Genome InSize OutSize -> io (Genome InSize OutSize, Genome InSize OutSize)
evalParent params datas' p@(MkGenome parentNet parentFit parentSFit) = do
    datas <- replicateA (batch params) (SSS15M.randomRead datas')
    -- ^ this can choose the same batch twice, but that's not too liekly, or a big deal

    -- copy parent and mutate
    childNet <- mutateNet params (copyNet parentNet)

    -- re-eval parent
    -- ps <- for datas $ \(inp,tar) => do
      -- (fit,res) <- eval' parentNet inp sumMoid tar
      -- pure fit
    -- eval copy
    -- putStrLn "parent loop end"
    (cs,res) <- unzip <$> traverse (\(inp,tar) => eval' childNet inp sumMoid tar) datas

    -- if reses are all the same this net is a complete bust
    (r :: rs) <- pure res
      | _ => pure (MkGenome parentNet parentFit parentSFit, MkGenome childNet minDouble minDouble)
    if all (arrEq r) rs
      then do
        -- putStrLn "all same"
        pure (MkGenome parentNet parentFit parentSFit, MkGenome childNet minDouble minDouble)
      else do
        -- putStrLn "not all same"
        -- printLn r
        -- lets try only caring about the worst result, as incentive to try harder always
        let cfr = minimum cs
        -- average fitnesses and apply stochasticity to improve exploration
        -- sfp <- stochasticFitness params pfr
        sfc <- stochasticFitness params cfr
        pure (MkGenome parentNet parentFit parentSFit, MkGenome childNet cfr sfc)
        -- pure (MkGenome parentNet sfp, MkGenome childNet sfc)


fraf : IORef (Maybe (Genome InSize OutSize, Genome InSize OutSize)) -> StateT (Bits64,Bits64) IO (Genome InSize OutSize, Genome InSize OutSize) -> IO ()
fraf ref st = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  res <- evalStateT (seed1,seed2) st
  writeIORef ref (Just res)

-- basetime 2010-01-01T00.000000000Z
-- randomTime : HasIO io => MonadState (Bits64,Bits64) io => io DateTime

pLoop : StochasticEval -> (parents : List (Genome InSize OutSize)) -> Array s (DArray InSize, DArray OutSize) -> StateT (Bits64,Bits64) IO (List (Genome InSize OutSize))
pLoop params parents datas = timeIt "pLoop" $ do
    evts <- liftIO $ for parents $ \p => do
      ref <- newIORef Nothing
      t <- fork (fraf ref (evalParent params datas p))
      pure (t,ref)
    Just evs <- liftIO $ map sequence $ for evts (\(t,ref) => threadWait t *> readIORef ref)
      | Nothing => putStrLn "evs failure" *> pure []
    -- evs <- for parents (evalParent params datas)
    -- evs consists of evaluated parent and child
    -- unzip them, concat, sort by fitness, and take (parentsCount params)
    let (pNets,cNets) = unzip evs
        nets = pNets ++ cNets
        sortedNets = sortOn @{Down} geneStochasticFitness nets -- sort best first
        finalNets = take (parentsCount params) sortedNets
    printLn $ map geneFitness finalNets
    pure finalNets

popLoop : StochasticEval -> (parents : List (Genome InSize OutSize)) -> Array s (DArray InSize, DArray OutSize) -> Nat -> StateT (Bits64,Bits64) IO (List (Genome InSize OutSize))
popLoop params parents datas Z = pure parents
popLoop params parents datas (S k) = do
    liftIO $ loopNo k
    res <- pLoop params parents datas
    popLoop params res datas k
  where
    loopNo : Nat -> IO ()
    loopNo n = putStrLn $ "Loops left: " ++ show n
-- I need to learn how to save nets now so I can work on them whenever

-- should probably start with sigmoid everywhere and bias 1 everywhere

export
stochasticXor : StochasticEval -> StateT (Bits64,Bits64) IO Double
stochasticXor params = do
    -- preget a bunch of trial data here and pass it along, getting trial data
    -- during evaluation is wicked expensive
    -- make an array of data and just pick batchNo of indexes at random

    -- funs <- fromList [logistic, logistic', relu, leakyRelu, swish]

    Just datas <- timeIt "main:get all datas" $ sequence <$> replicateA (dataSources params) getData
      | _ => putStrLn "data generation error" *> pure 0
    let (s ** training_data) = fromList' datas

    -- at some point I want to pull some bests-of from sql and use them as the starting pop
    parents <- replicateA (parentsCount params) (pure (MkGenome !randParent minDouble minDouble))
    -- traverse_ (\(MkGenome n _) => putStrLn (prettyNet n)) parents
    -- evolve parents for max evaluations
    bests' <- popLoop params parents training_data (maxEvaluations params)
    -- sort by real fitnes and then optimize
    bests <- popLoop params (sortOn @{Down} geneFitness bests') training_data (refiningEvaluations (record {mutRate = 0.03, stochasticity = 0.0, funcMutRate = 0.0} params))
    putStrLn "Bests:"
    printLn (map geneFitness bests)
    -- sort by real fitness
    g@(MkGenome bestNet f sf) :: (MkGenome bestNet2 f2 sf2) :: _ <- pure (sortOn @{Down} geneFitness bests)
      | _ => pure 0
    putStrLn "Best fitness:"
    printLn f
    
    -- printLn $ prettyNet bestNet

    -- evalParent' params training_data g

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp0,tar0) <- getData
      | _ => pure f
    let lasts0 = map (\ix => unsafeReadArray inp0 ix) (the (List Nat) [396,397,398,399])
    -- let lasts0 = map (\ix => unsafeReadArray inp0 ix) (the (List Nat) [0,1,2,3])
    (fit0,res0) <- eval' bestNet inp0 sumMoid tar0
    putStrLn "Last input:"
    printLn $ (mapArray (/multiplier) (fromList lasts0))
    putStrLn "Target:"
    printLn $ (mapArray (/multiplier) tar0)
    putStrLn "Result:"
    printLn $ (mapArray (/multiplier) res0)
    putStrLn "Fitness:"
    printLn fit0

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp1,tar1) <- getData
      | _ => pure f
    let lasts1 = map (\ix => unsafeReadArray inp1 ix) (the (List Nat) [396,397,398,399])
    -- let lasts1 = map (\ix => unsafeReadArray inp1 ix) (the (List Nat) [0,1,2,3])
    (fit1,res1) <- eval' bestNet inp1 sumMoid tar1
    putStrLn "Last input:"
    printLn $ (mapArray (/multiplier) (fromList lasts1))
    putStrLn "Target:"
    printLn $ (mapArray (/multiplier) tar1)
    putStrLn "Result:"
    printLn $ (mapArray (/multiplier) res1)
    putStrLn "Fitness:"
    printLn fit1

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp2,tar2) <- getData
      | _ => pure f
    let lasts2 = map (\ix => unsafeReadArray {a=Double} inp2 ix) (the (List Nat) [396,397,398,399])
    -- let lasts2 = map (\ix => unsafeReadArray inp2 ix) (the (List Nat) [0,1,2,3])
    (fit2,res2) <- eval' bestNet inp2 sumMoid tar2
    putStrLn "Last input:"
    printLn $ (mapArray (/multiplier) (fromList lasts2))
    putStrLn "Target:"
    printLn $ (mapArray (/multiplier) tar2)
    putStrLn "Result:"
    printLn $ (mapArray (/multiplier) res2)
    putStrLn "Fitness:"
    printLn fit2
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
