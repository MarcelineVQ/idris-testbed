module Data.Bits.Rotate

import Data.Fin
import Data.Bits

public export
interface Rotateable a where
  0 Index : Type
  rotateL : a -> Index -> a
  rotateR : a -> Index -> a

public export
Rotateable Bits8 where
  Index = Fin 8
  rotateL b s' = let s = (cast . finToNat) s' in prim__shl_Bits8 b s .|. prim__shr_Bits8 b (8 - s `mod` 8)
  rotateR b s' = let s = (cast . finToNat) s' in prim__shl_Bits8 b (8 - s `mod` 8) .|. prim__shr_Bits8 b s

public export
Rotateable Bits16 where
  Index = Fin 16
  rotateL b s' = let s = (cast . finToNat) s' in prim__shl_Bits16 b s .|. prim__shr_Bits16 b (16 - s `mod` 16)
  rotateR b s' = let s = (cast . finToNat) s' in prim__shl_Bits16 b (16 - s `mod` 16) .|. prim__shr_Bits16 b s

public export
Rotateable Bits32 where
  Index = Fin 32
  rotateL b s' = let s = (cast . finToNat) s' in prim__shl_Bits32 b s .|. prim__shr_Bits32 b (32 - s `mod` 32)
  rotateR b s' = let s = (cast . finToNat) s' in prim__shl_Bits32 b (32 - s `mod` 32) .|. prim__shr_Bits32 b s

public export
Rotateable Bits64 where
  Index = Fin 64
  rotateL b s' = let s = (cast . finToNat) s' in prim__shl_Bits64 b s .|. prim__shr_Bits64 b (64 - s `mod` 64)
  rotateR b s' = let s = (cast . finToNat) s' in prim__shl_Bits64 b (64 - s `mod` 64) .|. prim__shr_Bits64 b s
