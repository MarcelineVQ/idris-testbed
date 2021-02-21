module Data.Strong.IOMatrix

import Data.Strong.IOArray
import Data.IOArray.Prims

import Data.Fin
import public Data.Nat

-- export
-- record SIOMatrix (width : Nat) (height : Nat) a where
--   constructor MkSIOMatrix
--   natWidth : Nat
--   natHeightWidth : Nat
--   maxWidth : Int
--   maxHeight : Int
--   content : ArrayData a

-- Given that I've type-safed the interface it should be reasonable to remove much of the io from this module

public export
data SIOMatrix : (h : Nat) -> (w : Nat) -> Type -> Type where
  MkSIOMatrix : (rows : Nat) -> (cols : Nat) -> (maxHeight : Int) -> (maxWidth : Int)
             -> (content : ArrayData a) -> SIOMatrix rows cols a

export
content : SIOMatrix h w a -> ArrayData a
content (MkSIOMatrix _ _ _ _ c) = c

export
maxWidth : SIOMatrix h w a -> Int
maxWidth (MkSIOMatrix _ _ _ mw _) = mw

export
maxHeight : SIOMatrix h w a -> Int
maxHeight (MkSIOMatrix _ _ mh _ _) = mh


export
read : HasIO io => SIOMatrix h w a -> (row,col : Nat) -> (prf1 : LTE col w) => (prf2 : LTE row h) => io a
read mat row col = primIO (prim__arrayGet (content mat) (cast row * maxWidth mat + cast col))

export
write : HasIO io => SIOMatrix h w a -> (row,col : Nat) -> a -> LTE col w => LTE row h => io ()
write mat row col x = primIO (prim__arraySet (content mat) (cast row * maxWidth mat + cast col) x)

fef : (j : Nat) -> LTE j j
fef 0 = LTEZero
fef (S k) = LTESucc (fef k)

export
new : HasIO io => (rows,cols : Nat) -> (def : a) -> io (SIOMatrix rows cols a)
new rows cols def =
  pure $ MkSIOMatrix rows cols (cast rows) (cast cols) !(primIO (prim__newArray (cast rows * cast cols) def))

unsafeNew : HasIO io => (rows,cols : Nat) -> io (SIOMatrix rows cols a)
unsafeNew rows cols =
  pure $ MkSIOMatrix rows cols (cast rows) (cast cols) !(primIO (prim__newArray (cast rows * cast cols) (believe_me (the Int 0))))

export
newFillM : HasIO io => (rows,cols : Nat) -> ((r : Nat) -> (c : Nat) -> io a) -> io (SIOMatrix rows cols a)
newFillM rows cols g = do
      mat <- unsafeNew {a} rows cols
      case mat of
        MkSIOMatrix h w _ _ _ => do
          rowLoop h w mat {prf1 = fef h} {prf2 = fef w}
          pure mat
  where
    colLoop : (r : Nat) -> (c : Nat) -> SIOMatrix rows cols a -> (prf1 : LTE r rows) => (prf2 : LTE c cols) => io ()
    colLoop r 0 mat' = pure ()
    colLoop r (S c) mat' = do
      let p = lteSuccLeft prf2
      write mat' r c !(g r c)
      colLoop r c mat' {prf2 = p}
    rowLoop : (r : Nat) -> (w'' : Nat) -> (prf1 : LTE r rows) => (prf2 : LTE w'' cols) => SIOMatrix rows cols a -> io ()
    rowLoop 0 w'' mat' = pure ()
    rowLoop (S k) w'' mat' = do
      let p = lteSuccLeft prf1
      colLoop k w'' mat'
      rowLoop k w'' mat'

export
foldlMatrix : HasIO io => (b ->a -> b) -> b -> SIOMatrix rows cols a -> io (List b)
foldlMatrix f acc mat = do
      case mat of
        MkSIOMatrix h w _ _ _ => do
          rowLoop h w mat {prf1 = fef h} {prf2 = fef w}
  where
    colLoop : (r : Nat) -> (c : Nat) -> SIOMatrix rows cols a -> (prf1 : LTE r rows) => (prf2 : LTE c cols) => io b
    colLoop r 0 mat' = pure acc
    colLoop r (S c) mat' = do
      let p = lteSuccLeft prf2
      v <- read mat' r c
      rest <- colLoop r c mat'
      pure (f rest v)
    rowLoop : (r : Nat) -> (w'' : Nat) -> (prf1 : LTE r rows) => (prf2 : LTE w'' cols) => SIOMatrix rows cols a -> io (List b)
    rowLoop 0 w'' mat' = pure []
    rowLoop (S k) w'' mat' = do
      let p = lteSuccLeft prf1
      v <- colLoop k w'' mat'
      rest <- rowLoop k w'' mat'
      pure (rest ++ [v])
      -- [| colLoop k w'' mat' :: rowLoop k w'' mat' |]

-- modify : (i : Nat) -> LTE i j => (a -> b) -> SIOArray j a -> SIOArray j b

export
imapMatrixM : HasIO io => ((r : Nat) -> (c : Nat) -> a -> io b) -> SIOMatrix h w a -> io (SIOMatrix h w b)
imapMatrixM g mat = do
      case mat of
        MkSIOMatrix h w _ _ _ => do
          mat' <- unsafeNew {a=b} h w
          -- let d = 
          rowLoop h w mat' {prf1 = fef h} {prf2 = fef w}
          pure mat'
  where
    colLoop : (r : Nat) -> (c : Nat) -> SIOMatrix h w b -> (prf1 : LTE r h) => (prf2 : LTE c w) => io ()
    colLoop r 0 mat' = pure ()
    colLoop r (S c) mat' = do
      let p = lteSuccLeft prf2
      v <- read mat r c
      write mat' r c !(g r c v)
      colLoop r c mat' {prf2 = p}
    rowLoop : (r : Nat) -> (w'' : Nat) -> (prf1 : LTE r h) => (prf2 : LTE w'' w) => SIOMatrix h w b -> io ()
    rowLoop 0 w'' mat' = pure ()
    rowLoop (S k) w'' mat' = do
      let p = lteSuccLeft prf1
      colLoop k w'' mat'
      rowLoop k w'' mat'

-- issue is probably in vectMutlt' or zipWithArray or foldrArray
-- 

export
vectMult' : (Num a, HasIO io) => SIOMatrix h w a -> SIOArray w a -> io (SIOArray h a)
vectMult' mat arr = case mat of
    MkSIOMatrix h w _ _ _ => do
      arrr <- newArray h 0
      rowLoop h w arrr {prf1 = fef h} {prf2 = fef w}
      pure arrr
  where
    colLoop : (r : Nat) -> (c : Nat) -> (prf1 : LTE r h) => (prf2 : LTE c w) => io (List a)
    colLoop r 0 = pure []
    colLoop r (S c) = do
      let p = lteSuccLeft prf2
      mv <- read mat r c
      av <- readArray arr c
      [| pure (av * mv) :: colLoop r c {prf2 = p} |]
    rowLoop : (r : Nat) -> (w'' : Nat) -> (prf1 : LTE r h) => (prf2 : LTE w'' w) => SIOArray h a -> io ()
    rowLoop 0 w'' arr' = pure ()
    rowLoop (S k) w'' arr = do
        let p = lteSuccLeft prf1
        updrow <- colLoop k w''
        writeArray arr k (sum updrow)
        rowLoop k w'' arr

infixl 3 #>

export
%inline
(#>) : (Num a, HasIO io) => SIOMatrix h w a -> SIOArray w a -> io (SIOArray h a)
(#>) = vectMult'


export
toList : HasIO io => SIOMatrix h w a -> io (List (List a))
toList = foldlMatrix (\b,a => b ++ [a]) []

export
prettyMatrix : Show a => SIOMatrix h w a -> String
prettyMatrix m = show $ unsafePerformIO $ toList m

