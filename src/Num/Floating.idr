module Num.Floating

-- Probably overzelous with these constraints, this is all in service of making
-- working with arrays/matrices easier.
public export
interface (FromDouble ty, Neg ty, Fractional ty) => Floating ty where
  constructor MkFloating
  pi : ty
  euler : ty
  exp : ty -> ty
  log : ty -> ty
  pow : ty -> ty -> ty
  sin : ty -> ty
  cos : ty -> ty
  tan : ty -> ty
  asin : ty -> ty
  acos : ty -> ty
  atan : ty -> ty
  sinh : ty -> ty
  cosh : ty -> ty
  tanh : ty -> ty
  sqrt : ty -> ty
  floor : ty -> ty
  ceiling : ty -> ty

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
  tanh x = sinh x / cosh x -- can this NaN via cosh = 0?
  sqrt x = prim__doubleSqrt x
  floor x = prim__doubleFloor x
  ceiling x = prim__doubleCeiling x
