module Data.Bits.Bits128

import Data.Bits

export
record Bits128 where
  constructor MkB128
  high : Bits64
  low : Bits64

%inline
pointwise : (Bits64 -> Bits64 -> Bits64) -> Bits128 -> Bits128 -> Bits128
pointwise f x y = { high $= f y.high, low $= f y.low } x

export
Num Bits128 where
  (+) = ?dsffds
  (*) = ?dsffddss
  fromInteger x = MkB128 (fromInteger (x `div` 0xffffffffffffffff)) (fromInteger (x `mod` 0xffffffffffffffff))

export
Eq Bits128 where
  (==) x y = x.high == y.high && x.low == y.low

export
shiftL' : Bits128 -> Fin 128 -> Bits128
shiftL' x i' = let i = cast {to=Bits64} (finToNat i')
               in if i < 64
                    then {high := (x.high `prim__shl_Bits64` i) .|. (x.low `prim__shr_Bits64` (64 - i))
                         ,low  := x.low `prim__shl_Bits64` i
                         } x
                    else {high := (x.low `prim__shl_Bits64` (128 - i))
                         ,low  := 0
                         } x
-- shiftL' x i' = let i = cast {to=Bits64} (finToNat i')
  -- in if i > 63
       -- then { low := 0, high := prim__shl_Bits64 x.high (i - 63)} x
       -- else ?dsf

shiftR' : Bits128 -> Fin 128 -> Bits128

Bits Bits128 where
  Index       = Fin 128
  (.&.)       = pointwise prim__or_Bits64
  (.|.)       = pointwise prim__or_Bits64
  xor         = pointwise prim__xor_Bits64
  bit         = (1 `shiftL`)
  zeroBits    = MkB128 0 0
  testBit x i = (x .&. bit i) /= 0
  oneBits     = MkB128 0xffffffffffffffff 0xffffffffffffffff
  shiftL x    = shiftL' x --prim__shl_Bits64 x . cast . finToNat
  shiftR x    = shiftR' x --prim__shr_Bits64 x . cast . finToNat
