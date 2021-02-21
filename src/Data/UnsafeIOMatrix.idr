module Data.UnsafeIOMatrix

import Data.UnsafeIOArray
import Data.IOArray.Prims

import Data.Fin
import Data.Nat

export
record UIOMatrix a where
  constructor MkUIOMatrix
  maxWidth : Int
  maxHeight : Int
  content : ArrayData a

export
new : HasIO io => (width,height : Nat) -> (def : a) -> io (UIOMatrix a)
new width height def =
  pure $ MkUIOMatrix (cast width) (cast height) !(primIO (prim__newArray (cast width * cast height) def))

export
read : HasIO io => UIOMatrix a -> (i,j : Int) -> io a
read mat i j = primIO (prim__arrayGet (content mat) (cast i * maxHeight mat + cast j))

export
write : HasIO io => UIOMatrix a -> (i,j : Nat) -> a -> io ()
write mat i j x = primIO (prim__arraySet (content mat) (cast i * maxHeight mat + cast j) x)

export
vectMult : (Num a, HasIO io) => UIOArray a -> UIOMatrix a -> io (UIOArray a)
vectMult arr mat = do
  let i = maxWidth mat
      j = maxHeight mat
  arrr <- newArray j 0
  _ <- for [0..i-1] $ \row => do
         updrow <- for [0..j-1] $ \col => do
                     mv <- read mat row col
                     av <- readArray arr col
                     pure (av * mv)
         writeArray arrr row (sum updrow)
         pure ()
  pure arrr




