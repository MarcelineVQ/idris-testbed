module Net.Activations

import Data.Strong.IOArray

import public Num.Floating

public export
data Activations = Sigmoid | Relu | LeakyRelu | Tahn | Swish

record Activation where
  constructor MkActivation
  -- func : 

export
logistic : Floating a => a -> a
logistic x = 1 / (1 + exp (-x))

-- derivative of the logistic function
export
logistic' : Floating a => a -> a
logistic' x = logistic x * (1 - logistic x)

export
sigmoid : Floating a => a -> a
sigmoid = logistic

export
relu : (Num a, Ord a) => a -> a
relu = max 0

export
leakyRelu : (Ord a, Floating a) => a -> a
leakyRelu x = if x < 0 then x * 0.01 else x

export
swish : Floating a => a -> a
swish x = x * sigmoid x
