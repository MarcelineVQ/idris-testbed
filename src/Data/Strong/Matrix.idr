module Data.Strong.Matrix

import Data.Strong.Array
import Data.IOArray.Prims

import Data.Fin
import public Data.Nat

import Control.Monad.Identity

import Decidable.Equality
import JSON
import Generics.Derive
%language ElabReflection

public export
data Matrix : (h : Nat) -> (w : Nat) -> Type -> Type where
  MkMatrix : (rows : Nat) -> (cols : Nat) -> (maxHeight : Int) -> (maxWidth : Int)
             -> (content : ArrayData a) -> Matrix rows cols a

export
content : Matrix h w a -> ArrayData a
content (MkMatrix _ _ _ _ c) = c

export
maxWidth : Matrix h w a -> Int
maxWidth (MkMatrix _ _ _ mw _) = mw

export
maxHeight : Matrix h w a -> Int
maxHeight (MkMatrix _ _ mh _ _) = mh


-- 0 so I don't have to remember where to erase it
0 lteReflexive : (j : Nat) -> LTE j j
lteReflexive j = reflexive {x=j}

export
newMatrix : (h,w : Nat) -> (def : a) -> Matrix h w a
newMatrix rows cols def = unsafePerformIO $ do
    let intH = cast rows
        intW = cast cols
    pure $ MkMatrix rows cols intH intW !(primIO (prim__newArray (intH * intW) def))

export
newMatrix' : {h,w : Nat} -> (def : a) -> Matrix h w a
newMatrix' = newMatrix h w

export
newUnintializedMatrix : (h,w : Nat) -> Matrix h w a
newUnintializedMatrix h w = newMatrix h w (believe_me (the Int 0))

export
newUnintializedMatrix' : {h,w : Nat} -> Matrix h w a
newUnintializedMatrix' = newUnintializedMatrix h w

export
newMatrixCopy : Matrix h w a -> Matrix h w a
newMatrixCopy (MkMatrix h w ih iw contents) = unsafePerformIO $ do
    let new = newUnintializedMatrix h w
    copyFrom contents (content new) (ih * iw - 1)
    pure new
  where
    copyFrom : ArrayData elem ->
               ArrayData elem ->
               Int -> IO ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     copyFrom old new $ assert_smaller pos (pos - 1)

export
unsafeMutableWriteMatrix : HasIO io => Matrix h w a -> (row,col : Nat) -> a -> io ()
unsafeMutableWriteMatrix mat row col x = primIO (prim__arraySet (content mat) (cast row * maxWidth mat + cast col) x)

export
mutableWriteMatrix : HasIO io => Matrix h w a -> (row,col : Nat) -> a -> (0 prf1 : LTE row h) => (0 prf2 : LTE col w) => io ()
mutableWriteMatrix mat r c a = unsafeMutableWriteMatrix mat r c a

export
unsafeWriteMatrix : Matrix h w a -> (row,col : Nat) -> a -> Matrix h w a
unsafeWriteMatrix mat r c a =  unsafePerformIO $ do
  let new = newMatrixCopy mat
  unsafeMutableWriteMatrix new r c a
  pure new

export
writeMatrix : Matrix h w a -> (row,col : Nat) -> a -> (0 prf1 : LTE row h) => (0 prf2 : LTE col w) => Matrix h w a
writeMatrix mat r c a = unsafeWriteMatrix mat r c a

export
unsafeMutableReadMatrix : HasIO io => Matrix h w a -> (row,col : Nat) -> io a
unsafeMutableReadMatrix mat row col = primIO (prim__arrayGet (content mat) (cast row * maxWidth mat + cast col))

export
mutableReadMatrix : HasIO io => Matrix h w a -> (row,col : Nat) -> (0 prf1 : LTE row h) => (0 prf2 : LTE col w) => io a
mutableReadMatrix mat row col = unsafeMutableReadMatrix mat row col

export
unsafeReadMatrix : Matrix h w a -> (row,col : Nat) -> a
unsafeReadMatrix mat r c = unsafePerformIO $ unsafeMutableReadMatrix mat r c

export
readMatrix : Matrix h w a -> (row,col : Nat) -> (0 prf1 : LTE row h) => (0 prf2 : LTE col w) => a
readMatrix mat r c = unsafeReadMatrix mat r c

export
modifyMatrix : (a -> a) -> Matrix h w a -> (row,col : Nat) -> (0 prf1 : LTE row h) => (0 prf2 : LTE col w) => Matrix h w a
modifyMatrix f mat r c = writeMatrix mat r c (f (readMatrix mat r c))

export
imapMatrixM : Monad m => ((r : Nat) -> (c : Nat) -> a -> m b) -> Matrix h w a -> m (Matrix h w b)
imapMatrixM g mat = do
      case mat of
        MkMatrix h w _ _ _ => do
          let new = newUnintializedMatrix {a=b} h w
          rowLoop h w new {prf1 = lteReflexive h} {prf2 = lteReflexive w}
          pure new
  where
    colLoop : (r : Nat) -> (c : Nat) -> Matrix h w b -> (0 prf1 : LTE r h) => (0 prf2 : LTE c w) => m ()
    colLoop r 0 mat' = pure ()
    colLoop r (S c) mat' = do
      let 0 p = lteSuccLeft prf2
          v = readMatrix mat r c
          () = unsafePerformIO $ mutableWriteMatrix mat' r c !(g r c v)
      colLoop r c mat' {prf2 = p}
    rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r h) => (0 prf2 : LTE w'' w) => Matrix h w b -> m ()
    rowLoop 0 w'' mat' = pure ()
    rowLoop (S k) w'' mat' = do
      let 0 p = lteSuccLeft prf1
      colLoop k w'' mat'
      rowLoop k w'' mat'

export
imapMatrix : ((r : Nat) -> (c : Nat) -> a -> b) -> Matrix h w a -> Matrix h w b
imapMatrix g mat = runIdentity $ imapMatrixM (\r,c => Id . g r c) mat


-- extra copy, but easy to write
export
inewMatrixFillM : Monad m => (h,w : Nat) -> ((r : Nat) -> (c : Nat) -> m a) -> m (Matrix h w a)
inewMatrixFillM h w g = imapMatrixM (\r,c,_ => g r c) (newUnintializedMatrix {a} h w)

export
inewMatrixFill : (h,w : Nat) -> ((r : Nat) -> (c : Nat) -> a) -> Matrix h w a
inewMatrixFill h w g = runIdentity $ imapMatrixM (\r,c,_ => Id (g r c)) (newUnintializedMatrix {a} h w)

-- not really foldl of a matrix
export
foldlMatrix : (b -> a -> b) -> b -> Matrix rows cols a -> List b
foldlMatrix f acc mat = case mat of
    MkMatrix h w _ _ _ =>
     let 0 prf1 = lteReflexive h
         0 prf2 = lteReflexive w
     in rowLoop h w mat
  where
    colLoop : (r : Nat) -> (c : Nat) -> Matrix rows cols a -> (0 prf1 : LTE r rows) => (0 prf2 : LTE c cols) => b
    colLoop r 0 mat' = acc
    colLoop r (S c) mat' =
      let 0 p = lteSuccLeft prf2
          v = readMatrix mat' r c
          rest = colLoop r c mat'
      in  f rest v
    rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r rows) => (0 prf2 : LTE w'' cols) => Matrix rows cols a -> List b
    rowLoop 0 w'' mat' = []
    rowLoop (S k) w'' mat' =
      let 0 p = lteSuccLeft prf1
          v = colLoop k w'' mat'
          rest = rowLoop k w'' mat'
      in  rest ++ [v]

-- this should just visit every array value, we don't need a row/col based order
export
zipWithMatrix : (a -> b -> c) -> Matrix h w a -> Matrix h w b -> Matrix h w c
zipWithMatrix f mat1 mat2 = case mat1 of
            MkMatrix h w _ _ _ =>
              let new = newUnintializedMatrix {a=c} h w
                  0 prf1 = lteReflexive h
                  0 prf2 = lteReflexive w
              in rowLoop h w new
  where
    colLoop : (r : Nat) -> (col : Nat) -> Matrix h w c -> (0 prf1 : LTE r h) => (0 prf2 : LTE col w) => Matrix h w c
    colLoop r 0 mat' = mat'
    colLoop r (S col) mat' =
      let 0 p = lteSuccLeft prf2
          v1 = readMatrix mat1 r col
          v2 = readMatrix mat2 r col
          () = unsafePerformIO $ mutableWriteMatrix mat' r col (f v1 v2)
      in colLoop r col mat'
    rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r h) => (0 prf2 : LTE w'' w) => Matrix h w c -> Matrix h w c
    rowLoop 0 w'' mat' = mat'
    rowLoop (S k) w'' mat' =
      let 0 p = lteSuccLeft prf1
      in rowLoop k w'' (colLoop k w'' mat')

-- this could be more straightforward with vectors since we can just return a list of slices
export
toRows : Matrix rows cols a -> List (Array cols a)
-- toRows mat = case mat of
--     MkMatrix h w _ _ _ =>
--      let 0 prf1 = lteReflexive h
--          0 prf2 = lteReflexive w
--      in rowLoop h w mat
--   where
--     colLoop : (r : Nat) -> (c : Nat) -> Matrix rows cols a -> (0 prf1 : LTE r rows) => (0 prf2 : LTE c cols) => List a
--     colLoop r 0 mat' = []
--     colLoop r (S c) mat' =
--       let 0 p = lteSuccLeft prf2
--           v = readMatrix mat' r c
--           rest = colLoop r c mat'
--       in  rest ++ [v]
--     rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r rows) => (0 prf2 : LTE w'' cols) => Matrix rows cols a -> List (Array cols a)
--     rowLoop 0 w'' mat' = []
--     rowLoop (S k) w'' mat' =
--       let 0 p = lteSuccLeft prf1
--           v = colLoop k w'' mat'
--           rest = rowLoop k w'' mat'
--       in  rest ++ [Array.fromList v]

-- export
-- toList : Matrix rows cols a -> List (List a)
-- toList mat = Array.toList <$> toRows mat

-- export
-- foldlMatrix' : (b -> a -> b) -> b -> Matrix rows cols a -> b
-- foldlMatrix' f acc1 acc2 mat = case mat of
--     MkMatrix h w _ _ _ =>
--      let 0 prf1 = lteReflexive h
--          0 prf2 = lteReflexive w
--      in rowLoop h w mat
--   where
--     colLoop : (acc : b) -> (r : Nat) -> (c : Nat) -> Matrix rows cols a -> (0 prf1 : LTE r rows) => (0 prf2 : LTE c cols) => b
--     colLoop acc r 0 mat' = acc
--     colLoop acc r (S c) mat' =
--       let 0 p = lteSuccLeft prf2
--           v = readMatrix mat' r c
--           rest = colLoop r c mat'
--       in  f acc rest v
--     rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r rows) => (0 prf2 : LTE w'' cols) => Matrix rows cols a -> b
--     rowLoop 0 w'' mat' = acc1
--     rowLoop (S k) w'' mat' =
--       let 0 p = lteSuccLeft prf1
--           v = colLoop k w'' mat'
--           rest = rowLoop k w'' mat'
--       in f (colLoop k w'' mat') rest v

export
Functor (Matrix s a) where
  map f fa = imapMatrix (\_,_,a => f a) fa

export
vectMult : Num a => Matrix h w a -> Array w a -> Array h a
vectMult mat arr = case mat of
    MkMatrix h w _ _ _ =>
      let new = newArray h 0
          0 prf1 = lteReflexive h
          0 prf2 = lteReflexive w
      in  rowLoop h w new
  where
    colLoop : (r : Nat) -> (c : Nat) -> (0 prf1 : LTE r h) => (0 prf2 : LTE c w) => a
    colLoop r 0 = 0
    colLoop r (S c) =
      let 0 p = lteSuccLeft prf2
      in (readMatrix mat r c * readArray arr c) + colLoop r c
    rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r h) => (0 prf2 : LTE w'' w) => Array h a -> Array h a
    rowLoop 0 w'' arr' = arr'
    rowLoop (S k) w'' arr =
        let 0 p = lteSuccLeft prf1
            () = unsafePerformIO $ mutableWriteArray arr k (colLoop k w'')
        in  rowLoop k w'' arr

infixr 9 #>

export
%inline
(#>) : Num a => Matrix h w a -> Array w a -> Array h a
(#>) = vectMult

export
tr : Matrix h w a -> Matrix w h a
tr mat = case mat of
  MkMatrix h w _ _ _ =>
    imapMatrix (\r,c,_ => unsafeReadMatrix mat c r) newUnintializedMatrix' {a}

export
outer : Num a => Array n a -> Array m a -> Matrix n m a
outer arr1 arr2 = case (arr1,arr2) of
  (MkArray n _ _, MkArray m _ _) => imapMatrix (\r,c,_ => unsafeReadArray arr1 r * unsafeReadArray arr2 c) newUnintializedMatrix' {a}

-- outer f arr1 arr2 = case arr1 of
--             MkArray s _ _ =>
--               let new = newUnintializedMatrix {a=c} s s
--                   0 prf1 = lteReflexive h
--                   0 prf2 = lteReflexive w
--               in rowLoop h w new
--   where
--     colLoop : (r : Nat) -> (col : Nat) -> Matrix h w c -> (0 prf1 : LTE r h) => (0 prf2 : LTE col w) => Matrix h w c
--     colLoop r 0 mat' = mat'
--     colLoop r (S col) mat' =
--       let 0 p = lteSuccLeft prf2
--           v1 = readMatrix mat1 r col
--           v2 = readMatrix mat2 r col
--           () = unsafePerformIO $ mutableWriteMatrix mat' r col (f v1 v2)
--       in colLoop r col mat'
--     rowLoop : (r : Nat) -> (w'' : Nat) -> (0 prf1 : LTE r h) => (0 prf2 : LTE w'' w) => Matrix h w c -> Matrix h w c
--     rowLoop 0 w'' mat' = mat'
--     rowLoop (S k) w'' mat' =
--       let 0 p = lteSuccLeft prf1
--       in rowLoop k w'' (colLoop k w'' mat')

-- TODO: change me to dlist
export
toList : Matrix h w a -> List (List a)
toList mat = foldlMatrix (\b,a => b ++ [a]) [] mat

export
prettyMatrix : Show a => Matrix h w a -> String
prettyMatrix m = concat $ intersperse "\n" (show <$> Matrix.toList m)

export
ToJSON a => ToJSON (Matrix h w a) where
  toJSON = toJSON . Matrix.toList

{-

-- export
-- FromJSON a => FromJSON (s : Nat ** SIOArray s a) where
--   fromJSON = map fromList'' . fromJSON
-- 
-- export
-- {s:_} -> FromJSON a => FromJSON (SIOArray s a) where
--   fromJSON x = do
--     xs <- fromJSON {a=List a} x
--     case decEq (length xs) s of
--       (No contra) => fail "List length not correct, expected \{show s} got \{show (length xs)}"
--       (Yes Refl) => Right $ fromList''' xs
-- 

-}