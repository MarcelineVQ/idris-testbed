module Net.Activation

import Data.Strong.IOArray

import public Num.Floating

import Generics.Derive
%language ElabReflection

public export
data Activation = Sigmoid | Sigmoid' | Relu | LeakyRelu | Tanh | Swish

%runElab derive "Activation" [Generic,Meta,Eq,Ord,Show]

Range Activation where
  rangeFromTo r v = ?fweffsd
  rangeFromThenTo r v a = ?efeeeeww

  rangeFrom r = ?efewfe
  rangeFromThen r v = ?fewf

-- record Activation where
  -- constructor MkActivation
  -- func : 

export
%inline
logistic : Floating a => a -> a
logistic x = 1 / (1 + exp (-x))

-- derivative of the logistic function
export
%inline
logistic' : Floating a => a -> a
logistic' x = logistic x * (1 - logistic x)

export
%inline
sigmoid : Floating a => a -> a
sigmoid = logistic

export
%inline
relu : (Num a, Ord a) => a -> a
relu = max 0

export
%inline
leakyRelu : (Ord a, Floating a) => a -> a
leakyRelu x = if x < 0 then x * 0.01 else x

export
%inline
swish : Floating a => a -> a
swish x = x * sigmoid x

export
actList : List Activation
-- actList = [Sigmoid, Sigmoid', Relu, LeakyRelu, Tanh, Swish]
actList = [Sigmoid, Sigmoid', LeakyRelu, Swish]

export
%inline
actToFunc : (Ord a, Floating a) => Activation -> (a -> a)
actToFunc Sigmoid = logistic
actToFunc Sigmoid' = logistic'
actToFunc Relu = relu -- for some reason relu does weird-ass shit to nets, ignore it
actToFunc LeakyRelu = leakyRelu
actToFunc Tanh = Num.Floating.tanh -- tanh is slow it seems like
actToFunc Swish = swish
