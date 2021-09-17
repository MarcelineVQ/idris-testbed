module BP.Backprop.Interfaces

import Data.Strong.Array
import Data.Strong.Matrix

public export
interface Backprop a where
  constructor MkBackprop
  zero : a -> a
  one : a -> a
  add : a -> a -> a

export
Backprop Double where
  zero _ = 0.0
  one _ = 1.0
  add = (+)

export
Num a => Backprop (Array s a) where
  zero arr = const 0 <$> arr
  one arr = const 1 <$> arr
  add = (+)

export
Num a => Backprop (Matrix h w a) where
  zero mat = imapMatrix (\_,_,_ => 0) mat
  one mat = imapMatrix (\_,_,_ => 1) mat
  add = zipWithMatrix (+)

export
Backprop a => Backprop b => Backprop (a,b) where
  zero (a,b) = (zero a, zero b)
  one (a,b) = (one a, one b)
  add (x,y) (a,b) = (add x a, add y b)
