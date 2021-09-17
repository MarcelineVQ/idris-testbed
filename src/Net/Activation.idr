module Net.Activation

import Data.Strong.IOArray

import public Numeric.Floating

import Generics.Derive
%language ElabReflection

public export
data Activation = Sigmoid | Sigmoid' | Relu | LeakyRelu | Tanh | Swish | Negate | Mult

%runElab derive "Activation" [Generic,Meta,Eq,Ord,Show]

export
%inline
logistic : Neg a => Floating a => a -> a
logistic x = 1 / (1 + exp (-x))

-- derivative of the logistic function
export
%inline
logistic' : Neg a => Floating a => a -> a
logistic' x = logistic x * (1 - logistic x)

export
%inline
sigmoid : Neg a => Floating a => a -> a
sigmoid = logistic

export
%inline
relu : (Num a, Ord a) => a -> a
relu = max 0

export
%inline
leakyRelu : (FromDouble a, Ord a, Floating a) => a -> a
leakyRelu x = if x < 0 then x * 0.01 else x

export
%inline
swish : Neg a => Floating a => a -> a
swish x = x * sigmoid x

export
actList : List Activation
-- actList = [Sigmoid, Sigmoid', Relu, LeakyRelu, Tanh, Swish]
actList = [Tanh] --[Relu] --[LeakyRelu, Sigmoid, Sigmoid', Relu, Swish]

export
%inline
actToFunc : (FromDouble a, Neg a, Ord a, Floating a) => Activation -> (a -> a)
actToFunc Sigmoid = logistic
actToFunc Sigmoid' = logistic'
actToFunc Relu = relu -- for some reason relu does weird-ass shit to nets, ignore it
actToFunc LeakyRelu = leakyRelu
actToFunc Tanh = Numeric.Floating.tanh -- tanh is slow it seems like
actToFunc Swish = swish
-- linear funcs
actToFunc Negate = negate
actToFunc Mult = (*10)
