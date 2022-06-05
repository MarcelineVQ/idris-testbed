module System.Random.PRNG.Squares

import Data.Bits
import Data.DPair

import Data.Random.Source

import Control.Monad.State

-- import Util


-- counter-based prng
-- https://arxiv.org/pdf/2004.06278.pdf

-- Some convenience keys, should probably make up your own.
-- Any 64-bit cryptographically generated number is probably sufficient.
||| Key provided for convenience, there's more in Keys.idr
public export
%inline
key1 : Bits64
key1 = 0xa271dcb8746b9dcf

||| Key provided for convenience, there's more in Keys.idr
public export
%inline
key2 : Bits64
key2 = 0x839c215ba581ec4d

||| Key provided for convenience, there's more in Keys.idr
public export
%inline
key3 : Bits64
key3 = 0x9f532b4ed273fcb9

-- Minor minor utility for code size
fromNat' :  (k : Nat)
        -> {0 n : Nat} -- reduces code bloat compared to Data.Bits.fromNat
        -> {auto 0 prf : lt k n === True}
        -> Subset Nat (`LT` n)
fromNat' k = Element k (ltReflectsLT k n prf)

---------------------------------------------------

-- The paper mentions using `(ctr + 1) * key` instead of `ctr * key` to increase
-- uniformity, but doesn't specify if it means in the algorithm or merely that
-- used keys should be incremented by 1.

-- I'm not sure we have strictness analysys or whatever is needed to combine let
-- variables automatically so I'm writing this in direct style, expanded version
-- can be found as squares2.
||| `key` and `counter` combine to both become your seed and state at the same
||| time, but the majority of seeding is done by `key` and the majority of state
||| is `counter`. The idea is to increment `counter` for every new random number
||| you want. `key` should consist of a balance of 0 and 1 bits. You should
||| probably generate keys cryptographically, since they don't change often and
||| thus won't incur much cost.
||| A file "Keys.idr" is included for reference and convenience.
||| Refer to https://arxiv.org/abs/2004.06278 if the above reads as nonsense.
||| It's also useful to refer to "Parallel Random Numbers: As Easy As 1, 2, 3"
||| to understand the usefulness of counter-based PRNG.
export
squares : (key : Bits64) -> (counter : Bits64) -> Bits32
squares key ctr =
    let x = ctr * key
        z = x + key
    in cast $ square (                      -- Round 4
         rotate (square              -- Round 3
           (rotate (square           -- Round 2
             (rotate ( square x + x) -- Round 1
               ) + z)) + x)) + z
         `shiftR` thirtytwo
  where
    -- Don't `fromInteger 32` multiple times
    thirtytwo : Fin 64
    thirtytwo = 32
    square : Bits64 -> Bits64
    square z = z * z
    -- rotate by 32 bits
    rotate : Bits64 -> Bits64
    rotate z = shiftR z thirtytwo .|. shiftL z thirtytwo -- TODO: Is this really rotation?

-- The final rotation seems to result in Bits32 values?

-- Expanded version, close to the paper, the `y` variable isn't neccesary in an
-- immutable language. We don't really need the intermediate x's either, but
-- left for readability.
export
squares2 : (key : Bits64) -> (counter : Bits64) -> Bits32
squares2 key ctr = let x = cast ctr * key
                       z = x + key
                       x' = rotate (square x + x)        -- Round 1
                       x'' = rotate (square x' + z)      -- Round 2
                       x''' = rotate (square x'' + x)    -- Round 3
                   in cast $ square x''' + z `shiftR` thirtytwo -- Round 4
  where
    -- Don't `fromInteger 32` multiple times
    thirtytwo : Fin 64
    thirtytwo = 32
    square : Bits64 -> Bits64
    square z = z * z
    -- rotate by 32 bits
    rotate : Bits64 -> Bits64
    rotate z = shiftR z thirtytwo .|. shiftL z thirtytwo -- TODO: Is this really rotation?


export
%inline
gen : Bits64 -> Bits64 -> (incr : Bits64) -> (Bits32,Bits64)
gen key count incr = (squares key count, count+incr)

export
%inline
next : Bits64 -> Bits64 -> (Bits32,Bits64)
next key count = gen key count 1

-- normalize to (-1,1)
export
normalize : Bits32 -> Double
normalize v = cast {to = Double} (cast {to = Int32} v) / 2147483647 {- max Int32 bound -}

-- normalize to (0,1)
export
%inline
normalizeP : Bits32 -> Double
normalizeP v = abs $ normalize v

export
%inline
normalizePR : Double -> (Double,Double) -> Double
normalizePR d (lo,hi) = ((+ lo) . (* (hi - lo))) $ d

export
%inline
nextR : (key : Bits64) -> (counter : Bits64) -> (range : (Bits32,Bits32)) -> (Bits32,Bits64)
-- nextR key count (lo,hi) = let (r,c) = gen key count 1 in (lo + r * (hi - lo),c)

-- 2147483647 {- max Int32 bound -}
-- -2147483648 {- min Int32 bound -}

export
data SquaresGen : Type where
  MkSquaresGen : (key : Bits64) -> (counter: Bits64) -> SquaresGen

export
%inline
mkSquaresGen : (key : Bits64) -> (counter: Bits64) -> SquaresGen
mkSquaresGen = MkSquaresGen

-- nextS : (g : SquaresGen) => Bits32

export
Monad m => RandomSource m SquaresGen where
  getRandomWord32From (MkSquaresGen k c) = pure $ squares k c

-- export
-- %inline
-- nextSC : (sc : SquaresGen) => Bits32
-- nextSC = case sc of
--   MkSquaresGen key cntr => gen key cntr 1



{-

Data.Bits.fromNat wasn't erasing its implicit `n` argument. While this argument
was not used/computed it still ended up present in code, causing bloat.
This is particularly obvious with shiftL/R on Bits64 values.
Changing {n : Nat} to {0 n : Nat} results in scheme code like
(DataC-45Bits-fromNat (PreludeC-45Cast-u--cast_Cast_Int_Nat 32)))))))))))
instead of
(DataC-45Bits-fromNat (PreludeC-45Cast-u--cast_Cast_Int_Nat 32)
  (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 ... 64 total times

-}
