module Data.Strong.IOArray2

import Data.IOArray.Prims
import Data.Fin
import public Data.Nat
import Data.DPair

-- An IOArray of exact aent count

-- Not sure how else to extract size while retaining relation without exposing
-- constructor for casing
public export
data SArray : (size : Nat) -> Type -> Type where
  MkSArray : (size : Nat) -> (intSize : Int) -> (content : ArrayData a) -> SArray size a

export
size : SArray s a -> Int
size (MkSArray s intSize content) = intSize

content : SArray s a -> ArrayData a
content (MkSArray s intSize c) = c

export
unsafeNewArray : HasIO io => (s : Nat) -> io (SArray s a)
unsafeNewArray s = do
  let intsize = cast s
  arr <- primIO (prim__newArray intsize (believe_me (the Int 0)))
  pure (MkSArray s intsize arr)

export
newArray : HasIO io => (s : Nat) -> (def : a) -> io (SArray s a)
newArray s x = let intsize = cast s
               in pure (MkSArray s intsize !(primIO (prim__newArray intsize x)))

export
newArray' : (s : Nat) -> (def : a) -> SArray s a
newArray' s x = let intsize = cast s
                in MkSArray s intsize (unsafePerformIO $ primIO (prim__newArray intsize x))

export
writeArray : HasIO io => SArray s a -> (i : Nat) -> (prf : LTE i s) => a -> io ()
writeArray arr i x = primIO (prim__arraySet (content arr) (cast i) x)

export
readArray : HasIO io => SArray s a -> (i : Nat) -> (prf : LTE i s) => io a
readArray arr i = primIO (prim__arrayGet (content arr) (cast i))

export
readArray' : HasIO io => SArray s a -> (i : Nat) -> (prf : LTE i s) => io a
readArray' arr i = primIO (prim__arrayGet (content arr) (cast i))

export
modifyArray : HasIO io => (a -> a) -> SArray s a -> (i : Nat) -> LTE i s => io ()
modifyArray f arr i = do
  v <- readArray arr i
  writeArray arr i (f v)

fef : (j : Nat) -> LTE j j
fef 0 = LTEZero
fef (S k) = LTESucc (fef k)

export
newArrayFillM : HasIO io => (s : Nat) -> (Nat -> io a) -> io (SArray s a)
newArrayFillM s g = do
      new <- unsafeNewArray {a} s
      case new of
        MkSArray s _ _ => do
          go new s {prf = fef s}
          pure new
  where
    go : SArray s a -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do 
      let newprf = lteSuccLeft prf
      writeArray new k !(g k)
      go new k

export
foldrArray : (a -> b -> b) -> b -> SArray s a -> b
foldrArray f acc arr = case arr of
    MkSArray s _ _ => unsafePerformIO $ go s {prf = fef s}
  where
    go : HasIO io => (i : Nat) -> (prf : LTE i s) => io b
    go 0 = pure acc
    go (S k) = let p = lteSuccLeft prf in [| f (readArray arr k) (go k) |]

export
foldMapArray : Monoid b => (a -> b) -> SArray s a -> b
foldMapArray f arr = case arr of
    MkSArray s _ _ => unsafePerformIO $ go s {prf = fef s}
  where
    go : HasIO io => (i : Nat) -> (prf : LTE i s) => io b
    go 0 = f <$> readArray arr 0
    go (S k) = let p = lteSuccLeft prf in [| (f <$> readArray arr k) <+> go k |]

export
mapArray : (a -> b) -> SArray s a -> SArray s b
mapArray f arr = case arr of
    MkSArray s _ _ => unsafePerformIO $ do
      new <- unsafeNewArray {a=b} s
      go new s {prf = fef s}
      pure new
  where
    go : HasIO io => SArray s b -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = do
      v <- readArray arr 0
      writeArray new 0 (f v)
    go new (S k) = do
      let newprf = lteSuccLeft prf
      v <- readArray arr k
      writeArray new k (f v)
      go new k

export
imapArrayM : HasIO m => ((i : Nat) -> a -> m b) -> SArray s a -> m (SArray s b)
imapArrayM f arr = case arr of
    MkSArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      go new s {prf = fef s}
      pure new
  where
    go : SArray s b -> (i : Nat) -> (prf : LTE i s) => m ()
    go new 0 = do
      v <- readArray arr 0
      writeArray new 0 !(f 0 v)
    go new (S k) = do
      let newprf = lteSuccLeft prf
      v <- readArray arr k
      writeArray new k !(f k v)
      go new k

export
zipWithArray : (a -> b -> c) -> SArray s a -> SArray s b -> SArray s c
zipWithArray f arr1 arr2 = unsafePerformIO $ case arr1 of
    MkSArray s _ _ => do
      new <- unsafeNewArray {a=c} s
      go new s {prf = fef s}
      pure new
  where
    go : HasIO io => SArray s c -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = do
      v1 <- readArray arr1 0
      v2 <- readArray arr2 0
      writeArray new 0 (f v1 v2)
    go new (S k) = do
      let newprf = lteSuccLeft prf
      v1 <- readArray arr1 k
      v2 <- readArray arr2 k
      writeArray new k (f v1 v2)
      go new k


traverseArray : (HasIO io, Traversable f, Applicative f) => (a -> f b) -> SArray s a -> io (f (SArray s b))
traverseArray g arr = case arr of
    (MkSArray s intSize content) => do
      new <- unsafeNewArray {a = b} s
      go new 0
  where
    go : SArray s b -> (i : Nat) -> (prf : LTE i s) => io (f (SArray s b))
    go new 0 = do
      v <- readArray arr 0
      let c = g v
          -- e = traverse ?sdfd c
      writeArray new 0 ?sfdfsd
      pure (pure new)
    go new (S k) = ?fewf

export
toList : SArray s a -> List a
toList = foldrArray (::) []

fromList : HasIO io => (xs : List a) -> io (SArray (length xs) a)
fromList xs = do
    new <- unsafeNewArray {a} (length xs)
    go new xs (length xs) {prf = fef (length xs)}
    pure new
  where
    go : SArray (length xs) a -> (xs : List a) -> (i : Nat) -> (prf : LTE i (length xs)) => io ()
    go new [] 0 = pure ()
    go new [] (S k) impossible
    go new (x :: xs) Z = ?ssddfsfd_2
    go new (x :: xs) (S k) = ?sdfsfd_2

    -- go new (S k) = do
      -- let newprf = lteSuccLeft prf
      -- v1 <- readArray arr1 k
      -- v2 <- readArray arr2 k
      -- writeArray new k (f v1 v2)
      -- go new k

export
prettyArray : Show a => SArray s a -> String
prettyArray x = show (Data.Strong.IOArray2.toList x)

export
pointwise : Num a => SArray s a -> SArray s a -> SArray s a
pointwise = zipWithArray (+)

export
%inline
(+) : Num a => SArray s a -> SArray s a -> SArray s a
(+) = pointwise
