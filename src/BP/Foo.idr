module BP.Foo

import Numeric.Floating

import Util

import Generics.Derive
%language ElabReflection

public export
data D : Type -> Type -> Type where
  Dv : (v : a) -> (dv : a) -> D s a


-- %runElab derive "D" [Generic,Meta,Show]

infinitesimal : Num a => D s a
infinitesimal = Dv 0 1

export
lift : Num a => a -> D s a
lift v = Dv v 0


export
d : Num a => (forall s. D s a -> D s a) -> (a, a)
d f = let Dv y y' = f {s=()} infinitesimal
      in  (y,y')

export
Eq a => Eq (D s a) where
  Dv x _ == Dv y _ = x == y

export
Ord a => Ord (D s a) where
  compare (Dv x _) (Dv y _) = compare x y

export
Num a => Num (D s a) where
  Dv x dx + Dv y dy = Dv (x + y) (dx + dy)
  Dv x dx * Dv y dy = Dv (x * y) (dx * y + dy * x)
  fromInteger x = lift (fromInteger x)

export
Neg a => Neg (D s a) where
  Dv x dx - Dv y dy = Dv (x - y) (dx - dy)
  negate (Dv v dv) = Dv (negate v) (negate dv)

export
signum : (Ord a, Neg a) => a -> a
signum v = if v > 0 then 1 else if v == 0 then 0 else -1

namespace DSig
  signum : Ord a => Neg a => D s a -> D s a
  signum (Dv v _)  = lift (signum v)

export
Neg a => Ord a => Abs a => Abs (D s a) where
  abs (Dv v dv) = Dv (abs v) (signum v * dv)

export
Neg a => Ord a => Fractional a => Fractional (D s a) where
  x / y = x * recip y
  recip (Dv v dv) = Dv (recip v) (-dv / (v * v))

export
Num a => FromDouble a => FromDouble (D s a) where
  fromDouble x = lift (fromDouble x)

export
Fractional' : Type -> Type
Fractional' a = (Neg a, Ord a, Fractional a)

export
Num a => Num (a,a) where
  (x1,y1) * (x2,y2) = (x1 * x2, y1 * y2)
  (x1,y1) + (x2,y2) = (x1 + x2, y1 + y2)
  fromInteger x = (fromInteger x, fromInteger x)

export
Neg a => Ord a => Floating a => Floating (D s a) where
  pi = lift pi
  euler = lift euler
  exp (Dv b dv) = Dv (exp b) (dv * exp b)
  log (Dv v dv) = Dv (log v) (dv / v)
  sin (Dv v dv) = Dv (sin v) (dv * cos v)
  cos (Dv v dv) = Dv (cos v) (dv * (-(sin v)))
  tan (Dv v dv) = Dv (tan v) (dv / cos v ^ 2)
  asin (Dv v dv) = Dv (asin v) (dv / sqrt (1 - v * v))
  acos (Dv v dv) = Dv (acos v) (negate dv / sqrt (1 - v * v))
  -- acosh (Dv v dv) = Dv (acos v) (negate dv / sqrt (1 - v * v))
  atan (Dv v dv) = Dv (atan v) (dv / (v * v + 1))
  -- atanh (Dv v dv) = Dv (atan v) (dv / (v * v + 1))
  sinh (Dv v dv) = Dv (sinh v) (dv * cosh v)
  cosh (Dv v dv) = Dv (cosh v) (dv * sinh v)
  tanh (Dv v dv) = Dv (tanh v) (dv / cosh v ^ 2)
  sqrt (Dv v dv) = Dv (sqrt v) (dv / (2 * sqrt v))
  -- pow  (Dv 0 0) (Dv y _) = Dv (0 `pow` a) 0
  -- pow  _        (Dv 0 0) = Dv 1 0
  -- x ** ForwardDouble y 0 = lift1 (**y) (\z -> y *^ z ** Id (y - 1)) x
  pow (Dv x dx) (Dv y dy) =
    let a = x `pow` y
        (dadb, dadc) = (y * a / x,  a * log x)
        da = dadb * dx + dy * dadc
    in Dv a da


export
curve : Neg a => Ord a => Fractional a => D s a -> D s a
curve v = v ^ 2 / 4

export
reflect : (Neg a, Ord a, Fractional a) => a -> a
reflect v = let (y,y') = d (\h => curve (lift v + h))
            in  y + v * (recip y' - y') / 2

export
diff' : Num a => (forall s. D s a -> D s a) -> a -> (a, a)
diff' f x = let Dv y y' = f {s=()} (Dv x 1)
            in  (y,y')

export
diff : Num a => (forall s. D s a -> D s a) -> a -> a
diff f x = snd $ diff' f x

data Wenger : Type where
  

export
foo : D s Double -> D s Double -> D s Double
foo x y = x * y + sin x



