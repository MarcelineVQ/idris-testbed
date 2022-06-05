module Net.SSSRec15M

-- module made to learn how to evolve a 15 minute oracle

import Oanda.ToDB

import Decidable.Equality

import Control.Monad.Managed

import Net.RecNN

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

import System.ConcurrentMap

import Util

import TimeIt

import System.Random.Types

public export
record StochasticEval where
  constructor MkStochasticEval
  stochasticity : Double
  mutRate : Double
  funcMutRate : Double
  perturbProb : Double
  parentsCount : Nat
  maxEvaluations : Nat
  concurrentEvaluations : Nat
  refiningEvaluations : Nat
  randomlyVaryingInitialCondition : Bool
  maxFitness : Double
  batch : Nat -- number of tests to average for fitness
  dataSources : Nat

public export
defaultStochasticEval : StochasticEval
defaultStochasticEval = MkStochasticEval
  0.1 -- stochasticity
  0.05 -- mutRate -- mutrate should go down the larger your net is
  0.01 -- funcMutRate
  0.5 -- perturbProb    -- half chance of mut half of perturb
  20 -- parentsCount
  500 -- maxEvaluations
  8 -- concurrentEvaluations
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
InSize = 4

%tcinline
OutSize : Nat
OutSize = 4

NetShape : Type
-- NetShape = RecNetwork InSize [20,20,8] OutSize
-- NetShape = RecNetwork InSize (replicate 10 4 ++ [10,4]) OutSize
-- NetShape = RecNetwork InSize [4,8,12,8,8,8,8,8,8,4] OutSize
-- NetShape = RecNetwork InSize (replicate 60 4) OutSize
-- NetShape = RecNetwork InSize (replicate 5 12) OutSize
-- NetShape = RecNetwork InSize (replicate 10 12) OutSize
-- NetShape = RecNetwork InSize (replicate 100 2) OutSize
NetShape = RecNetwork InSize (replicate 10 2) OutSize
-- NetShape = RecNetwork InSize ([12,10,8,4] ++ replicate 80 2 ++ [3,3,4]) OutSize

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

-- I need to move eval to a step at a time, so I can compute error each step, and have a net that runs indefinetly computing a new error each step

-- this is io just for debugging really
stepEval : HasIO io => {i,o:_} -> RecNetwork i hs o -> (input : DArray i) -> (target : DArray o) -> io (RecNetwork i hs o, Double, DArray o)
stepEval net input target = do
  let (new,r) = stepNet net input
      diff = zipWithArray (-) target r
      errs = toList $ mapArray (\x => squared (x / multiplier)) diff
      err = sum errs -- we used to use min, but it seemed to create nets that got stuck on a single answer for any question
  pure (new, err, r)
  -- note this returns the error, not the fitness

-- this should probably discard the errors of the first n steps, where n is the
-- size of the net, because history starts at 0 for each layer
-- err is the total of errors of every timestep, fitness is 1 - that total
eval : HasIO io => {o:_} -> RecNetwork o hs o -> (input : List (DArray o)) -> (target : DArray o) -> io (Double, DArray o)
eval net inputs target = mapFst (\x => 1 - x) <$> eval' (0, newArray' 0) net inputs
  where
    eval' : (Double, DArray o) -> RecNetwork o hs o -> (input : List (DArray o)) -> io (Double, DArray o)
    eval' r net' [] = pure r
    eval' (errs,rs) net' [x] = do
      (_,err,r) <- stepEval net' x target
      pure (errs + err, r)
    eval' (errs,rs) net' (x :: tar :: xs) = do
      (new,err,r) <- stepEval net' x tar
      eval' (errs + err, r) new xs

-- evaluate a network and return the squared error
-- computer based on a scaling multiplier, but scale back down error
-- eval : HasIO io => {i,o:_} -> RecNetwork i hs o -> (input : List (DArray i)) -> (target : DArray o) -> io (Double, DArray o)
-- eval net inputs target = do
--   (new, errs, rs) <- foldlM (\(new, errs,rs),inp => ?sddfs) (net,Prelude.Nil,Prelude.Nil) inputs
-- 
--   let fitness = sum errs
--       r = List.last rs
--   -- let r = runNet (net, newArray' 0.0) input
--   --     diff = zipWithArray (-) target r
--   --     errs = Array.toList $ mapArray (\x => squared (x / multiplier)) diff
--   --     fitness = 1 - sum errs -- choose the worstestsest, to promote all answers being right
--   pure (fitness, r)

randomRead : HasIO io => MonadState (Bits64,Bits64) io => Array s a -> io a
randomRead arr = do
  let c = cast $ !nextRandW `mod` cast (size arr)
  unsafeMutableReadArray arr c

randomRead' : HasIO io => MonadState (Bits64,Bits64) io => Array s a -> io (Nat,a)
randomRead' arr = do
  let c = cast $ !nextRandW `mod` cast (size arr)
  pure $ (c,!(unsafeMutableReadArray arr c))

randomFun : HasIO io => MonadState (Bits64,Bits64) io => io Activation
randomFun = SSSRec15M.randomRead (fromList actList)

randomFuns : HasIO io => MonadState (Bits64,Bits64) io => {s : _} -> io (Array s Activation)
randomFuns = inewArrayFillM s (\_ => SSSRec15M.randomFun)

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
zeroWeights : HasIO io => MonadState (Bits64,Bits64) io => {i,o : _} -> io (Weights i o)
zeroWeights = [| MkWeights (inewArrayFillM _ (\_ => pure 0.0)) randomMat |]

export
neutralWeights : HasIO io => MonadState (Bits64,Bits64) io => {i,o : _} -> io (Weights i o)
neutralWeights = [| MkWeights (inewArrayFillM _ (\_ => pure 1.0)) randomMat |]

export
zeroRecWeights : HasIO io => MonadState (Bits64,Bits64) io => {o : _} -> io (RecWeights o)
zeroRecWeights = [| MkRecWeights (inewArrayFillM _ (\_ => pure 1.0)) (inewArrayFillM _ (\_ => pure 0.0)) |]

export
randomNet : HasIO io => MonadState (Bits64,Bits64) io => {i,hs,o : _} -> io (RecNetwork i hs o)
randomNet {hs = []} = [| O randomWeights zeroRecWeights |]
randomNet {hs = _ :: _} = [| L SSSRec15M.randomFun randomWeights (randomNet) zeroRecWeights |]

neutralNet : HasIO io => MonadState (Bits64,Bits64) io => {i,hs,o : _} -> io (RecNetwork i hs o)
neutralNet {hs = []} = [| O zeroWeights zeroRecWeights |]
neutralNet {hs = _ :: _} = [| L SSSRec15M.randomFun zeroWeights neutralNet zeroRecWeights |]


copyRecWeights : RecWeights o -> RecWeights o
copyRecWeights w = MkRecWeights (newArrayCopy (wWeights w)) (newArrayCopy (wInp w))

copyWeights : Weights i o -> Weights i o
copyWeights w = MkWeights (newArrayCopy (wBias w)) (newMatrixCopy (wNodes w))

-- array is immutable now, I don't need this
copyNet : RecNetwork i hs o -> RecNetwork i hs o
copyNet (O w pre) = O (copyWeights w) (copyRecWeights pre)
copyNet (L a w y pre) = L a (copyWeights w) (copyNet y) (copyRecWeights pre)

-- 100 input bars of open,high,low,close. 5 ouputs, the predictions of the coming candles
-- I might need relu/swish here to allow for larger values
export
randParent : HasIO io => MonadState (Bits64,Bits64) io => io (NetShape)
randParent = randomNet

neutralParent : HasIO io => MonadState (Bits64,Bits64) io => io (NetShape)
neutralParent = neutralNet

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
    then SSSRec15M.randomFun
    else pure f

-- perturbProb is the prob that a mutation, if it occurs, is a perturbation
mutateWeights : HasIO io => MonadState (Bits64,Bits64) io => (mutProb : Double) -> (perturbProb : Double) -> Weights i o -> io (Weights i o)
mutateWeights mutProb perturbProb (MkWeights wBias wNodes) =
    let mut = mutate mutProb perturbProb
    in [| MkWeights (imapArrayM (\_,v => mut v) wBias) (imapMatrixM (\_,_,v => mut v) wNodes) |]

-- dont' mutate wBias here, it's state.
mutateRecWeights : HasIO io => MonadState (Bits64,Bits64) io => (mutProb : Double) -> (perturbProb : Double) -> RecWeights o -> io (RecWeights o)
mutateRecWeights mutProb perturbProb pre =
    let mut = mutate mutProb perturbProb
    in [| MkRecWeights (imapArrayM (\_,v => mut v) (wWeights pre)) (pure $ wInp pre) |]

mutateNet : HasIO io => MonadState (Bits64,Bits64) io => StochasticEval -> RecNetwork i hs o -> io (RecNetwork i hs o)
mutateNet params net = go net
  where
    go : forall i,hs,o. RecNetwork i hs o -> io (RecNetwork i hs o)
    go (O w pre) = [| O (mutateWeights (mutRate params) (perturbProb params) w) (mutateRecWeights (mutRate params) (perturbProb params) pre) |]
    go (L a w l pre) = [| L (mutFuns (funcMutRate params) a) (mutateWeights (mutRate params) (perturbProb params) w) (go l) (mutateRecWeights (mutRate params) (perturbProb params) pre) |]

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
getData : HasIO io => MonadState (Bits64,Bits64) io => Nat -> io (Maybe (List (DArray 4), DArray 4))
getData num = timeIt "getData" $ do
    -- start <- show <$> nextRandRW (0,280000)  -- random number roughly between 0 and db size - 100
    -- start <- show . (`mod`280000) <$> nextRandW -- random number roughly between 0 and db size - 100
    start <- show . (`mod` (74043 - cast num)) <$> nextRandW -- random number roughly between 0 and db size - 100
    -- liftIO $ putStrLn start
    let count = show (num + 1) -- show (z + 1) -- "101" -- we want 5 extra as targets
        sql = "where granularity = \"H1\" and instrument = \"USD_CAD\" order by opentime limit \{start},\{count}"
    -- putStrLn sql
    input' <- liftIO $ getCandles'' sql
    
    -- need to write this and eval to get going with recurrents
    
    let (inputs,targets) = splitAt num input'
        -- (is ** input)  = (map  (fromList' . sqlCandleMids) inputs')
        -- (ts ** target) = fromList' (map sqlCandleMids targets')
        inputs = map (fromList' . map ((* multiplier) . cast {to=Double}) . sqlCandleMids) inputs
        targets = map (fromList' . map ((* multiplier) . cast {to=Double}) . sqlCandleMids) targets
        input  = fraf inputs
        
    -- printLn input
    -- printLn target
    Just target <- pure $ fraf targets
      | Nothing => pure Nothing
    (target ::_ ) <- pure target -- it would't let me pair this with Just, above
      | _ => pure Nothing
    pure $ [| MkPair input (Just target) |]
  where
    fraf : List (n : Nat ** DArray n) -> Maybe (List (DArray 4))
    fraf xs = for xs $ \(s ** xs) => case decEq s 4 of
      No contra => Nothing
      Yes Refl => Just xs

evalParent : HasIO io => MonadState (Bits64,Bits64) io => StochasticEval -> List (List (DArray InSize), DArray OutSize) -> RecGenome InSize OutSize -> io (RecGenome InSize OutSize, RecGenome InSize OutSize)
evalParent params datas p@(MkRecGenome parentNet parentFit parentSFit) = do
    -- copy parent and mutate, shouldn't need copy now that arrays are immutable
    childNet <- mutateNet params (copyNet parentNet)

    (cs,res) <- unzip <$> traverse (\(inp,tar) => eval childNet inp tar) datas
    
    -- if reses are all the same this net is a complete bust
    (r :: rs) <- pure res
      | _ => pure (MkRecGenome parentNet parentFit parentSFit, MkRecGenome childNet minDouble minDouble)
    if length res > 1 && all (r ==) rs
      then do
        -- putStrLn "all same"
        pure (MkRecGenome parentNet parentFit parentSFit, MkRecGenome childNet minDouble minDouble)
      else do
        -- let cfr = sum cs
        -- let cfr = average cs
        -- let pfr = average ps
        let cfr = sum cs
        -- input should include time since we're doing time series now
        
        -- average fitnesses and apply stochasticity to improve exploration
        sfc <- stochasticFitness params cfr
        pure (MkRecGenome parentNet parentFit parentSFit, MkRecGenome childNet cfr sfc)
        -- pure (MkRecGenome parentNet sfp, MkRecGenome childNet sfc)

-- wrapper for forking parent evaulation, currently ruins reproducability however due to new seeds
fraf' : StateT (Bits64,Bits64) IO (RecGenome InSize OutSize, RecGenome InSize OutSize) -> IO (RecGenome InSize OutSize, RecGenome InSize OutSize)
fraf' st = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  evalStateT (seed1,seed2) st

pLoop : StochasticEval -> (parents : List (RecGenome InSize OutSize)) -> Array s (List (DArray InSize), DArray OutSize) -> StateT (Bits64,Bits64) IO (List (RecGenome InSize OutSize))
pLoop params parents datas' = timeIt "pLoop" $ do
    datas <- replicateA (batch params) (SSSRec15M.randomRead datas')
    -- ^ this can choose the same batch twice, but that's not too liekly, or a big deal
    evs <- liftIO $ mapNConcurrently (concurrentEvaluations params) (fraf' . evalParent params datas) parents
    -- evs consists of evaluated parent and child
    -- unzip them, concat, sort by fitness, and take (parentsCount params)
    let (pNets,cNets) = unzip evs
        nets = pNets ++ cNets
        sortedNets = sortOn @{Down} geneStochasticFitness nets -- sort best first
        finalNets = take (parentsCount params) sortedNets
    printLn $ map geneFitness finalNets
    pure finalNets

popLoop : StochasticEval -> (parents : List (RecGenome InSize OutSize)) -> Array s (List (DArray InSize), DArray OutSize) -> Nat -> StateT (Bits64,Bits64) IO (List (RecGenome InSize OutSize))
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

stochasticXor' : List (List (DArray InSize), DArray OutSize) -> StochasticEval -> StateT (Bits64,Bits64) IO Double
stochasticXor' datas params = do
    let (s ** training_data) = fromList' datas
    -- at some point I want to pull some bests-of from sql and use them as the starting pop
    parents <- replicateA (parentsCount params) (pure (MkRecGenome !neutralParent minDouble minDouble))
    -- evolve parents for max evaluations
    bests' <- popLoop params parents training_data (maxEvaluations params)
    -- sort by real fitnes and then optimize
    bests <- popLoop params (sortOn @{Down} geneFitness bests') training_data (refiningEvaluations (record {mutRate = 0.01, stochasticity = 0.0, funcMutRate = 0.0} params))
    putStrLn "Bests:"
    printLn (map geneFitness bests)
    -- sort by real fitness
    g@(MkRecGenome bestNet f sf) :: (MkRecGenome bestNet2 f2 sf2) :: _ <- pure (sortOn @{Down} geneFitness bests)
      | _ => pure 0
    -- printLn f
    pure f

export
stochasticXor : StochasticEval -> StateT (Bits64,Bits64) IO Double
stochasticXor params = do
    Just datas <- timeIt "main:get all datas" $ sequence <$> replicateA (dataSources params) (getData 100)
      | _ => putStrLn "data generation error" *> pure 0
    let (s ** training_data) = fromList' datas

    -- at some point I want to pull some bests-of from sql and use them as the starting pop
    parents <- replicateA (parentsCount params) (pure (MkRecGenome !neutralParent minDouble minDouble))
    -- evolve parents for max evaluations
    bests' <- popLoop params parents training_data (maxEvaluations params)
    -- sort by real fitnes and then optimize
    bests <- popLoop params (sortOn @{Down} geneFitness bests') training_data (refiningEvaluations (record {mutRate = 0.01, stochasticity = 0.0, funcMutRate = 0.0} params))
    putStrLn "Bests:"
    printLn (map geneFitness bests)
    -- sort by real fitness
    g@(MkRecGenome bestNet f sf) :: (MkRecGenome bestNet2 f2 sf2) :: _ <- pure (sortOn @{Down} geneFitness bests)
      | _ => pure 0
    putStrLn "Best fitness:"
    printLn f
    
    -- printLn $ prettyNet bestNet

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp0,tar0) <- getData 100
      | _ => pure f
    -- let lasts0 = map (\ix => unsafeReadArray inp0 ix) (the (List Nat) [396,397,398,399])
    -- let lasts0 = map (\ix => unsafeReadArray inp0 ix) (the (List Nat) [0,1,2,3])
    (fit0,res0) <- eval bestNet inp0 tar0
    -- putStrLn "Last input:"
    -- printLn $ (mapArray (/multiplier) (fromList lasts0))
    putStrLn "Target:"
    printLn $ (mapArray (/multiplier) tar0)
    putStrLn "Result:"
    printLn $ (mapArray (/multiplier) res0)
    putStrLn "Fitness:"
    printLn fit0

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp1,tar1) <- getData 100
      | _ => pure f
    -- let lasts1 = map (\ix => unsafeReadArray inp1 ix) (the (List Nat) [396,397,398,399])
    -- let lasts1 = map (\ix => unsafeReadArray inp1 ix) (the (List Nat) [0,1,2,3])
    (fit1,res1) <- eval bestNet inp1 tar1
    -- putStrLn "Last input:"
    -- printLn $ (mapArray (/multiplier) (fromList lasts1))
    putStrLn "Target:"
    printLn $ (mapArray (/multiplier) tar1)
    putStrLn "Result:"
    printLn $ (mapArray (/multiplier) res1)
    putStrLn "Fitness:"
    printLn fit1

    -- putStrLn $ prettyNet bestNet

    -- i also want to know what the 100th candle was, for comparison
    -- gen some data and try it
    Just (inp2,tar2) <- getData 100
      | _ => pure f
    -- let lasts2 = map (\ix => unsafeReadArray {a=Double} inp2 ix) (the (List Nat) [396,397,398,399])
    -- let lasts2 = map (\ix => unsafeReadArray inp2 ix) (the (List Nat) [0,1,2,3])
    (fit2,res2) <- eval bestNet inp2 tar2
    -- putStrLn "Last input:"
    -- printLn $ (mapArray (/multiplier) (fromList lasts2))
    putStrLn "Target:"
    printLn $ (mapArray (/multiplier) tar2)
    putStrLn "Result:"
    printLn $ (mapArray (/multiplier) res2)
    putStrLn "Fitness:"
    printLn fit2

    pure $ average [fit0,fit1,fit2]



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

4:     RecGenome[p][g] <- rand(-8.0, 8.0)

5:   Fitness[p] <- evaluate (p)

6:   NEvaluations <- NEvaluations + NTrials

  // evolution is continued until a maximum number of evaluation trials is performed

7: while(NEvaluations < MaxEvaluations) do

8:   for p <- 0 to NParents do

     // in the randomly varying experimental condition parents are re-evaluated

9:    if (RandomlyVaryingInitialCondition) then

10:     Fitness[p] <- evaluate (p)

11:     NEvaluations <- NEvaluations + NTrials

12:    RecGenome[p+NParents] <- RecGenome[p] // create a copy of parents’ RecGenome

13:    mutate-RecGenome(p+NParents) // mutate the genotype of the offspring

14:    Fitness[p+Nparents] <- evaluate[p+NParents]

15:    NEvaluations <- NEvaluations + NTrials

   // noise ensures that parents are replaced by less fit offspring with a low probability

16:      NoiseFitness[p] <- Fitness[p] * (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))

17:    NoiseFitness[p+NParents] <-

         Fitness[p+NParents] * (1.0 + rand(-Stochasticity*MaxFit, Stochasticity*MaxFit))

     // the best among parents and offspring become the new parents

18:  rank RecGenome[NParents*2] for NoiseFitness[NParents*2]

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

export
runStochastic : StochasticEval -> IO ()
runStochastic params = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  _ <- runStateT (seed1,seed2) $ do
    _ <- stochasticXor params
    pure ()
  pure ()

-- The thing to watch for is fitness over 1 when it prints the final bests, 1+
-- will get every xor correct.
-- runs and popsize have similar impact on fitness
export
runStochasticSet : Int -> StochasticEval -> IO ()
runStochasticSet runs params = do
  seed1 <- cast {from=Int} {to=Bits64} <$> randomIO
  seed2 <- cast {from=Int} {to=Bits64} <$> randomIO
  -- let seed1 = 1236941894
  -- let seed2 = 1977147118
  let paramslist =
        --  record {stochasticity = 0.10, mutRate = 0.01, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.10, mutRate = 0.02, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.10, mutRate = 0.03, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.10, mutRate = 0.50, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.10, mutRate = 0.10, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.03, mutRate = 0.02, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.07, mutRate = 0.02, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.10, mutRate = 0.02, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.15, mutRate = 0.02, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        -- ,record {stochasticity = 0.20, mutRate = 0.02, batch = 2, parentsCount = 20, maxEvaluations = 500, refiningEvaluations = 0, dataSources = 50, funcMutRate = 0.0} defaultStochasticEval
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.0, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.1, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.2, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.3, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.4, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.5, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.6, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.7, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.8, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 0.9, funcMutRate = 0.0} params ::
        record {stochasticity = 0.10, mutRate = 0.02, batch = 2, perturbProb = 1.0, funcMutRate = 0.0} params ::
        []
  -- let paramslist' = zip [1 .. Prelude.List.length paramslist] paramslist
  _ <- runStateT (seed1,seed2) $ do -- don't use stochasticXor here, call directly so you can pass the same data just once
    Just datas <- timeIt "main:get all datas" $ sequence <$> replicateA (dataSources params) (getData 100)
      | _ => putStrLn "data generation error" *> pure []
    rs <- for [1 .. runs] $ \_ => for paramslist (stochasticXor' datas)
    let rs' = zip [1 .. List.length paramslist] (average <$> List.transpose rs)
    traverse printLn rs'
  pure ()

export
runTest : IO ()
runTest = runStochastic defaultStochasticEval

main : IO ()
main = runStochastic $ record {batch = 4, parentsCount = 15, maxEvaluations = 5} defaultStochasticEval
