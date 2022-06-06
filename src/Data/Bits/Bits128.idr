module Data.Bits.Bits128

import Data.Bits

import Data.Bits.Rotate

-- No reason to not export this
public export
record Bits128 where
  constructor MkB128
  high : Bits64
  low : Bits64

%inline
shiftL' : Bits128 -> Fin 128 -> Bits128
shiftL' x i' = let i = cast {to=Bits64} (finToNat i')
               in if i < 64
                    then {high := (x.high `prim__shl_Bits64` i) .|. (x.low `prim__shr_Bits64` (63 - i))
                         ,low  := x.low `prim__shl_Bits64` i
                         } x
                    else {high := (x.low `prim__shl_Bits64` (i-64))
                         ,low  := 0
                         } x

%inline
shiftR' : Bits128 -> Fin 128 -> Bits128
shiftR' x i' = let i = cast {to=Bits64} (finToNat i')
               in if i < 64
                    then {low := (x.high `prim__shl_Bits64` (63 + i)) .|. (x.low `prim__shr_Bits64` i)
                         ,high  := x.high `prim__shr_Bits64` i
                         } x
                    else {low := (x.high `prim__shr_Bits64` (i-64))
                         ,high  := 0
                         } x

%inline
pointwise : (Bits64 -> Bits64 -> Bits64) -> Bits128 -> Bits128 -> Bits128
pointwise f x y = { high $= f x.high, low $= f x.low } y

export
Num Bits128 where
  x + y = let l = x.low + y.low
              h = x.high + y.high + (if l < x.low then 1 else 0)
          in MkB128 h l
  -- This should probably mod first as well to cap the size of the literal
  -- TODO: NB: This hasn't been checked to account negative literals
  fromInteger x = MkB128 (fromInteger (x `div` (0x10000000000000000)))
                         (fromInteger (x `mod` (0x10000000000000000)))
  x * y = ?bigOof

export
Eq Bits128 where
  (==) x y = x.high == y.high && x.low == y.low

export
Ord Bits128 where
  compare x y = case compare x.high y.high of
    EQ => compare x.low y.low
    r  => r
--  compare x y = compare x.high y.high <+> compare x.low y.low
-- ^ cute but wasteful

public export
Bits Bits128 where
  Index       = Fin 128
  (.&.)       = pointwise prim__or_Bits64
  (.|.)       = pointwise prim__or_Bits64
  xor         = pointwise prim__xor_Bits64
  bit         = (1 `shiftL`)
  zeroBits    = MkB128 0 0
  testBit x i = (x .&. bit i) /= 0
  oneBits     = MkB128 0xffffffffffffffff 0xffffffffffffffff
  shiftL      = shiftL'
  shiftR      = shiftR'

export
Neg Bits128 where
  x - y = x + negate y
  negate r = (complement zeroBits `xor` r) + 1

-- Copied from Prelude.Num but I don't actually understand what `abs` means for
-- bits since they're absolute values by definition.
export
Abs Bits128 where
  abs x = if x < 0 then -x else x

-- Not sure how to generalize this to any Bits since we lose the knowlege of
-- what Index is, and thus how to provide a value to shiftR, since there's no
-- requirement for Index to be a number. Or any particular requirements at all.
%inline
export -- count shifts to get to MSB
getMSBIndex : Bits128 -> Fin 128
getMSBIndex b = if b == 0 then FZ else getMSBIndex' b
  where
    getMSBIndex' : Bits128 -> Fin 128
    getMSBIndex' b = if b == 1 then FZ else finS $ getMSBIndex' (shiftR b 1)

-- check for 0 on both sides of these first
export
Integral Bits128 where
  div x y = ?dsfsfd
  mod x y = ?fefsdf

export
Show Bits128 where
  show b = show $ let r = cast {to=Integer} b.high * 0xffffffffffffffff in r * r + cast b.low

public export
FiniteBits Bits128 where
  popCount = ?dsfsd
  bitsToIndex = ?dsdsfsd
  bitSize = ?dsfddsfs

public export
Rotateable Bits128 where
  Index = Fin 128
  rotateL b s' = shiftL b s' .|. shiftR b (127 - s')
  rotateR b s' = shiftR b s' .|. shiftL b (127 - s')
