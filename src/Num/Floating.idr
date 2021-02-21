module Num.Floating

-- Probably overzelous with these constraints, this is all in service of making
-- working with arrays/matrices easier.
public export
interface (FromDouble a, Neg a, Fractional a) => Floating a where
  pi : a
  euler : a
  exp : a -> a
  log : a -> a
  pow : a -> a -> a
  sin : a -> a
  cos : a -> a
  tan : a -> a
  asin : a -> a
  acos : a -> a
  atan : a -> a
  sinh : a -> a
  cosh : a -> a
  tanh : a -> a
  sqrt : a -> a
  floor : a -> a
  ceiling : a -> a

export
Floating Double where
  pi = 3.14159265358979323846
  euler = 2.7182818284590452354
  exp x = prim__doubleExp x
  log x = prim__doubleLog x
  pow x y = exp (y * log x) -- prim__doublePow x y
  sin x = prim__doubleSin x
  cos x = prim__doubleCos x
  tan x = prim__doubleTan x
  asin x = prim__doubleASin x
  acos x = prim__doubleACos x
  atan x = prim__doubleATan x
  sinh x = (exp x - exp (-x)) / 2
  cosh x = (exp x + exp (-x)) / 2
  tanh x = sinh x / cosh x
  sqrt x = prim__doubleSqrt x
  floor x = prim__doubleFloor x
  ceiling x = prim__doubleCeiling x
