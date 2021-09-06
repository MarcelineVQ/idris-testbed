module Net.Types

import public Data.Strong.IOMatrix
import public Data.Strong.IOArray

import Net.Activation

import JSON
import Generics.Derive
%language ElabReflection

-- SIOArray of Doubles
public export
DArray : Nat -> Type
DArray n = SIOArray n Double

public export
record Weights (i : Nat) (o : Nat) where
  constructor MkWeights
  wBias : SIOArray o Double
  wNodes : SIOMatrix o i Double

%runElab derive "Weights" [Generic,Meta]

{-
Now, a Weights linking an m-node layer to an n-node layer has an n-dimensional
bias vector (one component for each output) and an n-by-m node weight matrix
(one column for each output, one row for each input).
-}
public export
data Network : Nat -> List Nat -> Nat -> Type where
  O : Weights i o -> Network i [] o
  L : Activation -> Weights i h -> Network h hs o -> Network i (h :: hs) o

public export
record Genome (i : Nat) (o : Nat) where
  constructor MkGenome
  geneNet : Network i hs o
  geneFitness : Double
  geneStochasticFitness : Double

export
prettyWeights : Weights i o -> String
prettyWeights (MkWeights wBias wNodes) = prettyArray wBias ++ "\n" ++ prettyMatrix wNodes

export
prettyNet : Network i hs o -> String
prettyNet (O x) = prettyWeights x
prettyNet (L a x y) = show a ++ "\n" ++ prettyWeights x ++ "\n" ++ prettyNet y

export
prettyGenome : Genome i o -> String
prettyGenome (MkGenome net f sf) = "MkGenome " ++ prettyNet net ++ " " ++ show f ++ " " ++ show sf

