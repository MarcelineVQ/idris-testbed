module Data.Vector

import Data.IOArray.Prims
import Data.Nat

import Data.Fin

-- I actually need to track the slice data as well as overall data

export
data Vector : Nat -> Type -> Type where
  MkVector : (start : Int) -> (len : Nat) -> (arrSize : Int) ->
             ArrayData a -> Vector len a

-- newArray : (n : Nat) -> (n ** ArrayData a)
-- newArray = ?asSDFfsd
-- primIO $ prim__newArray



data FinOrLTE : Type where

slice : Vector s a -> (start : Int) -> (len : Nat) -> LTE len s => Vector len a
slice (MkVector k s arrSize x) start len = MkVector (k+start) len arrSize x

index : Vector s a -> (i : Int) -> a
index x i = ?indasex_rhs



