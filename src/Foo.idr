module Foo

import public Data.IOMatrix

import public Data.Strong.IOMatrix
import public Data.UnsafeIOMatrix
import public Data.UnsafeIOArray

import public System.Random.Natural

-- Brand new weight
export
randWeight : HasIO io => io Double
randWeight = randomRIO (-8,8)

-- Perturb an existing weight
export
perturbWeight : HasIO io => Double -> io Double
perturbWeight w = do
  let v = !twelve + w
  pure $ if v > 8
           then 8
           else if v < -8
                  then -8
                  else v

-- I want to predict what x bars from now will be, lets say 10 bars

-- most direct choice is feed-forward on 100 bars at once, with
-- high,low,open,close per bar. This means our input layer is 400 wide

-- wrapping
data SMatrix : (m : Nat) -> (n : Nat) -> Type -> Type where
  MkSMatrix : (m,n : Nat) -> IOMatrix a -> SMatrix m n a

export
unsmatrix : SMatrix m n a -> IOMatrix a
unsmatrix (MkSMatrix m n x) = x

{-
Now, a Weights linking an m-node layer to an n-node layer has an n-dimensional
bias vector (one component for each output) and an n-by-m node weight matrix
(one column for each output, one row for each input).
-}

data Net : Nat -> List Nat -> Nat -> Type where
  Z : SMatrix i o Double -> Net i hs o
  S : SMatrix i h Double -> Net i hs o -> Net i (h :: hs) o

export
randomWeights : HasIO io => (m,n : Nat) -> io (SMatrix m n Double)
randomWeights m n = pure $ MkSMatrix m n !(newFill (cast m) (cast n) randWeight)

export
randomNet : HasIO io => (i : Nat) -> (hs : List Nat) -> (o : Nat) -> io (Net i hs o)
randomNet i [] o = Z <$> randomWeights i o
randomNet i (h :: hs) o = [| S (randomWeights i h) (randomNet i hs o) |]

-- example net, 100 inputs, 3 hidden layers, 2 outputs
export
egNet : Net 100 [20,10,5] 2
egNet = ?dsffd

logistic : Double -> Double
logistic x = 1 / (1 + exp (-x))

{-
runLayer :: Weights -> Vector Double -> Vector Double
runLayer (W wB wN) v = wB + wN #> v
-}
runLayer : SMatrix i o Double -> SMatrix i _ Double -> List Double
runLayer (MkSMatrix i o x) (MkSMatrix i _ y)
  = ?dfsfds

runNet : Net i hs o -> SMatrix i _ Double -> SMatrix _ o Double
runNet (Z x) input = ?runNet_rhs_1
runNet (S x y) input = ?runNet_rhs_2


data Genome : Type where
  MkGenome : (weights : IOMatrix Double) -> Net i hs o -> Genome

data Child : Type where
  MkChild : Genome -> Child

data Parent : Type where
  MkParent : Genome -> Parent



{-

The Stochastic Steady State (SSS) is a (μ + μ) evolutionary strategy [49] that operates on the basis of populations formed by μ parents. During each generation each parent generates one offspring, the parent and the offspring are evaluated, and the best μ individuals are selected as new parents (see the pseudo-code below). It is a method developed by us that belongs to the class of methods proposed by [14–15]. The novelty with respect to previous related methods consists in the introduction of the Stochasticity parameter that permits to regulate the selective pressure. This is obtained by adding to the fitness of individuals a value randomly selected in the range [-Stochasticity*MaxFitness, Stochasticity*MaxFitness] with a uniform distribution. When this parameter is set to 0.0 only the best μ individuals are allowed to reproduce. The higher the value of the parameter is, the higher the probability that other individuals reproduce is. For a discussion of evolutionary optimization in uncertain environments and in the presence of a noisy fitness function see [51].

SSS Method:

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

In the experiment reported in this paper the connection weights are evolved and the topology of the network is kept fixed. The initial population is encoded in a matrix of μ x θ real numbers that are initialized randomly with a uniform distribution in the range [-8.0, 8.0], where μ corresponds to the number of parent and θ corresponds to the total number of weights and biases. Offspring are generated by creating a copy of the genotype of the parent and by subjecting each gene to mutation with a MutRate probability. Mutations are realized by replacing or perturbing a gene value with equal probability. Replacements are realized by substituting the gene with a new real number randomly generated within the range [-8.0, 8.0] with a uniform distribution. Perturbations are realized by adding to the current value of a gene a real number randomly selected with a Gaussian distribution with a standard deviation of 1.0 and a mean of 0.0. Values outside the [-8.0, 8.0] range after perturbations are truncated in the range.

This method requires setting two parameters: MutRate and Stochasticity. To identify the optimal values of the parameters we systematically varied MutRate in the range [1%, 3%, 5%, 7%, 10%, 15% and 20%] and Stochasticity in the range [0%, 10%, 20%, 30%, 40%, 50%, 70%, and 100%]. Population size was set to 20. To enhance the ability of the method to refine the evolved candidate solutions, we reduced the mutation rate to 1% and we set the Stochasticity to 0% during the last 1/20 period of the evolutionary process.

-}