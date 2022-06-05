module Net.AFSSS15M

-- module made to learn how to evolve a 15 minute oracle

import Oanda.ToDB

import Decidable.Equality

import Control.Monad.Managed

import public Net.AFFFNN

import Data.Buffer

import Data.ArrayFire

-- import Net.Types

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

import System.Random.Types

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


public export
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

export
defaultStochasticEval : StochasticEval
defaultStochasticEval = MkStochasticEval
  0.02 -- stochasticity
  0.03 -- mutRate -- mutrate should go down the larger your net is
  0.01 -- funcMutRate
  0.5 -- perturbProb    -- half chance of mut half of perturb
  20 -- parentsCount
  500 -- maxEvaluations
  100 -- refiningEvaluations
  True -- randomlyVaryingInitialCondition
  1 -- maxFitness
  4 -- batch
  20 -- dataSources

multiplier : Double
multiplier = 1

-- in and out must be multiples of 4
%tcinline
InSize : Nat
InSize = 400

%tcinline
OutSize : Nat
OutSize = 4

NetShape : Type
-- NetShape = Network InSize (replicate 20 12) OutSize
-- NetShape = Network InSize ([100,100,100,20,12,8]) OutSize 
NetShape = Network InSize ([400,400,400,400,400,100,100,50,25,25] ++ replicate 10 12)  OutSize
-- NetShape = Network InSize [20] OutSize
-- NetShape = Network InSize [20,12] OutSize

average : List Double -> Double
average xs = sum xs / cast (length xs)

%inline
minDouble : Double
minDouble = -1.797e308

square : {s:_} -> Arr s -> Arr s
square x = x * x

export
minimum : List Double -> Double
minimum = foldr min 1.797e308

-- evaluate a network and return the squared error
-- we could multiple the array by a coefficient array to bias later guesses
-- 1 might be a bad basis, USD_CAD isn't far from it in the first place
eval : RandomEngine => {i,o:_} -> Network i hs o -> (input : Arr i) -> (target : Arr o) -> (Double, Arr o)
eval net input target =
  let r = runNet net input
      diff = target - r
      errs = 1 - square diff
      fitness'' = getScalarD $ minimum errs
  in (fitness'', r)

-- 100 input bars of open,high,low,close. 5 ouputs, the predictions of the coming candles
-- I might need relu/swish here to allow for larger values
export
randParent : RandomEngine => NetShape
randParent = randomNet _ _ _

-- neutralParent : HasIO io => MonadState (Bits64,Bits64) io => io (NetShape)
-- neutralParent = neutralNet

export
randD : HasIO io =>  (eng : RandomEngine) => io Double
randD = pure $ getScalarD $ randomUniform'' {dt=F64} {dims = [1]}

export
randD' : (eng : RandomEngine) => Double
randD' = getScalarD $ randomUniform'' {dt=F64} {dims = [1]}

export
randDR : (eng : RandomEngine) => (Double,Double) -> Double
randDR (lo,hi) = lo + randD' * (hi - lo)

export -- normal dist
randND : HasIO io => (eng : RandomEngine) => io Double
randND = pure $ getScalarD $ randomNormal'' {dt=F64} {dims = [1]}

export
randB64 : HasIO io => (eng : RandomEngine) => io Bits64
randB64 = getScalarB64 <$> randomUniformIO eng U64 [1]

-- push array to buffer, send buffer to arr
arrayToArr : HasIO io => Array s Double -> io (Arr s)
arrayToArr arr = do
  let (MkArray s intSize content) = arr
  let bufsize = size_of_double * intSize
  Just b <- newBuffer bufsize
    | _ => pure $ believe_me 1.2
  -- We have to compute the skip ourselves :/
  for_ [0,size_of_double .. bufsize - 1] $ \i => do
    v <- unsafeMutableReadArray arr (cast (i `div` size_of_double))
    setDouble b i v
  pure $ createArray b F64 _

export
mutate' : {dims:_} -> (eng : RandomEngine) => (mutProb : Double) -> (perturbProb : Double) -> AFArray dims F64 -> AFArray dims F64
mutate' mutProb perturbProb arr =
  -- mutate, perturb 
  let cond1 = randomUniform' `le` fromDouble mutProb -- decide which slots mutate
      cond2 = cond1 `and` (randomUniform' `le` fromDouble perturbProb) -- decide which mutate slots instead perturb
      arr' = clamp (-2) 2 (arr + randomNormal'')
  in select cond2 arr' (select cond1 randomUniform'' arr)
  -- select is really really slow, can we do this without so many extra arrays?

mutFuns : HasIO m => MonadState (Bits64,Bits64) m => (mutProb : Double) -> Activation -> m Activation
-- mutFuns mutProb f = do
--   if !randomNormalP <= mutProb
--     then SSS15M.randomFun
--     else pure f

-- perturbProb is the prob that a mutation, if it occurs, is a perturbation
mutateWeights : {i,o:_} -> RandomEngine => (mutProb : Double) -> (perturbProb : Double) -> Weights i o -> Weights i o
mutateWeights mutProb perturbProb (MkWeights wBias wNodes) =
    MkWeights (mutate' mutProb perturbProb wBias) (mutate' mutProb perturbProb wNodes)

mutateNet : RandomEngine => {i,o:_} -> StochasticEval -> Network i hs o -> Network i hs o
mutateNet params (O x) = O (mutateWeights (mutRate params) (perturbProb params) x)
mutateNet params (L x y) = L (mutateWeights (mutRate params) (perturbProb params) x) (mutateNet params y)

-- (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))
stochasticFitness : RandomEngine => StochasticEval -> Double -> Double
stochasticFitness params fitness =
  let range = stochasticity params * maxFitness params
  in fitness * (1 + randDR (-range,range))

-- randBit : MonadState (Bits64,Bits64) io => io Double
-- randBit = pure $ if !nextRand > 0 then 1.0 else 0.0



-- get data is slow slow slow
getData : RandomEngine => HasIO io => {i,o : _} -> io (Maybe (Arr i, Arr o))
getData = timeIt "getData" $ do
    let candlecount = 18856
        lookahead = 5
        z = cast {to=Bits64} i `div` 4
        start = show . (`mod` (candlecount - z)) $ !randB64 -- random number roughly between 0 and db size - 100
        count = show (z + lookahead) -- "101" -- we want 5 extra as targets
        sql = "where granularity = \"H4\" and instrument = \"USD_CAD\" order by opentime limit \{start},\{count}"
    input' <- liftIO $ getCandles'' sql
    let (inputs,targets) = splitAt (cast z) input'
        inputs'  = (* multiplier) . cast {to=Double} <$> concatMap sqlCandleMids inputs
        targets' = (* multiplier) . cast {to=Double} <$> concatMap sqlCandleMids (drop (cast (lookahead - 1)) targets)
        (is ** input)  = fromList' inputs'
        (ts ** target) = fromList' targets'
    -- printLn input
    -- printLn target
    l <- arrayToArr input
    r <- arrayToArr target
    case (decEq is i, decEq ts o) of
      (Yes Refl, Yes Refl) => pure $ Just (l,r)
      _ => pure Nothing

evalParent : RandomEngine => StochasticEval -> List (Arr InSize, Arr OutSize) -> Genome InSize OutSize -> (Genome InSize OutSize, Genome InSize OutSize)
evalParent params datas p@(MkGenome parentNet parentFit parentSFit) =
    -- copy parent and mutate
    let childNet = mutateNet params parentNet
        -- eval copy
        (cs,res) = unzip $ map (\(inp,tar) => eval childNet inp tar) datas
        -- lets try only caring about the worst result, as incentive to try harder always
        cfr = minimum cs
        -- apply stochasticity to improve exploration
        sfc = stochasticFitness params cfr
        -- restochas parent too, for exploration
        sfp = stochasticFitness params parentFit
        -- sfc = cfr
    in (MkGenome parentNet parentFit parentSFit, MkGenome childNet cfr sfc)
    -- pure (MkGenome parentNet sfp, MkGenome childNet sfc)

-- basetime 2010-01-01T00.000000000Z
-- randomTime : HasIO io => MonadState (Bits64,Bits64) io => io DateTime

randomRead : HasIO io => RandomEngine => Array s a -> io a
randomRead arr = do
  let MkArray _ intSize _ = arr
  pure $ unsafeReadArray arr (cast (!randB64 `mod` cast intSize))

fraf : IORef (Maybe (Genome InSize OutSize, Genome InSize OutSize)) -> (Genome InSize OutSize, Genome InSize OutSize) -> IO ()
fraf ref act = writeIORef ref (Just act)

pLoop : HasIO io => RandomEngine => StochasticEval -> (parents : List (Genome InSize OutSize)) -> Array s (Arr InSize, Arr OutSize) -> io (List (Genome InSize OutSize))
pLoop params parents datas' = timeIt "pLoop" $ do
    datas <- replicateA (batch params) (randomRead datas')
    -- evs <- for parents (evalParent params datas)
    -- ^ this can choose the same batch twice, but that's not too liekly, or a big deal
    evs <- liftIO $ mapConcurrently 8 (pure . evalParent params datas) parents
    -- evs <- for parents (evalParent params datas)
    -- evs consists of evaluated parent and child
    -- unzip them, concat, sort by fitness, and take (parentsCount params)
    let (pNets,cNets) = unzip evs
        nets = pNets ++ cNets
        sortedNets = sortOn @{Down} geneStochasticFitness nets -- sort best first
        finalNets = take (parentsCount params) sortedNets
    printLn $ map geneFitness finalNets
    pure finalNets

popLoop : RandomEngine => StochasticEval -> (parents : List (Genome InSize OutSize)) -> Array s (Arr InSize, Arr OutSize) -> Nat -> StateT (Bits64,Bits64) IO (List (Genome InSize OutSize))
popLoop params parents datas Z = pure parents
popLoop params parents datas (S k) = do
    liftIO $ loopNo k
    res <- pLoop params parents datas
    popLoop params res datas k
  where
    loopNo : Nat -> IO ()
    loopNo n = putStrLn $ "Loops left: " ++ show n
-- I need to learn how to save nets now so I can work on them whenever

export
stochasticXor : RandomEngine => StochasticEval -> StateT (Bits64,Bits64) IO Double
stochasticXor params = do
    -- preget a bunch of trial data here and pass it along, getting trial data
    -- during evaluation is wicked expensive
    -- make an array of data and just pick batchNo of indexes at random

    -- funs <- fromList [logistic, logistic', relu, leakyRelu, swish]

    Just datas <- timeIt "main:get all datas" $ sequence <$> replicateA (dataSources params) (timeIt "datagetting" $ getData)
      | _ => putStrLn "data generation error" *> pure 0
    let (s ** training_data) = fromList' datas

    -- at some point I want to pull some bests-of from sql and use them as the starting pop
    parents <- replicateA (parentsCount params) (pure (MkGenome randParent minDouble minDouble))
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
    -- let lasts0 = map (\ix => unsafeReaArr inp0 ix) (the (List Nat) [396,397,398,399])
    -- let lasts0 = map (\ix => unsafeReaArr inp0 ix) (the (List Nat) [0,1,2,3])
    let (fit0,res0) = eval bestNet inp0 tar0
    -- putStrLn "Last input:"
    -- printLn $ (mapArray (/multiplier) (fromList lasts0))
    putStrLn "Target:"
    printLn $ tar0 / fromDouble multiplier
    putStrLn "Result:"
    printLn $ res0 / fromDouble multiplier
    putStrLn "Fitness:"
    printLn fit0

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp1,tar1) <- getData
      | _ => pure f
    -- let lasts1 = map (\ix => unsafeReaArr inp1 ix) (the (List Nat) [396,397,398,399])
    -- let lasts1 = map (\ix => unsafeReaArr inp1 ix) (the (List Nat) [0,1,2,3])
    let (fit1,res1) = eval bestNet inp1 tar1
    -- putStrLn "Last input:"
    -- printLn $ (mapArray (/multiplier) (fromList lasts1))
    putStrLn "Target:"
    printLn $ tar1 / fromDouble multiplier
    putStrLn "Result:"
    printLn $ res1 / fromDouble multiplier
    putStrLn "Fitness:"
    printLn fit1

    -- putStrLn $ prettyNet bestNet

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp2,tar2) <- getData
      | _ => pure f
    -- let lasts2 = map (\ix => unsafeReaArr {a=Double} inp2 ix) (the (List Nat) [396,397,398,399])
    -- let lasts2 = map (\ix => unsafeReaArr inp2 ix) (the (List Nat) [0,1,2,3])
    let (fit2,res2) = eval bestNet inp2 tar2
    -- putStrLn "Last input:"
    -- printLn $ (mapArray (/multiplier) (fromList lasts2))
    putStrLn "Target:"
    printLn $ tar2 / fromDouble multiplier
    putStrLn "Result:"
    printLn $ res2 / fromDouble multiplier
    putStrLn "Fitness:"
    printLn fit2

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
  seed <- cast {from=Int} {to=Bits64} <$> randomIO
  Right eng <- afCreateRandomEngine AF_RANDOM_ENGINE_DEFAULT seed
    | Left err => printLn err

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
main = runStochastic 1 $ record {batch = 4, parentsCount = 5, maxEvaluations = 50, refiningEvaluations = 10} defaultStochasticEval
