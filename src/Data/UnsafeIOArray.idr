module Data.UnsafeIOArray

import Data.IOArray.Prims
import Data.Fin

-- An IOArray of exact element count

export
record UIOArray elem where
  constructor MkUIOArray
  maxSize : Int
  content : ArrayData elem

export
size : UIOArray a -> Int
size = maxSize

export
newArray : HasIO io => (s : Int) -> (def : elem) -> io (UIOArray elem)
newArray s x = let size = cast s
               in pure (MkUIOArray size !(primIO (prim__newArray size x)))

export
writeArray : HasIO io => UIOArray elem -> (i : Int) -> elem -> io ()
writeArray arr i x = primIO (prim__arraySet (content arr) (cast i) x)

export
readArray : HasIO io => UIOArray elem -> (i : Int) -> io elem
readArray arr i = primIO (prim__arrayGet (content arr) (cast i))

export
readArray' : HasIO io => UIOArray elem -> (i : Int) -> io elem
readArray' arr i = primIO (prim__arrayGet (content arr) (cast i))

export
modifyArray : HasIO io => (a -> a) -> UIOArray a -> (i : Int) -> io ()
modifyArray f arr i = do
  v <- readArray arr i
  writeArray arr i (f v)




