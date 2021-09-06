module Data.Strong.IOArray

import Data.IOArray.Prims
import Data.Fin
import public Data.Nat
import Data.DPair


import Num.Floating

import Data.List

import System.Random

import Util

import Decidable.Equality
import JSON
import Generics.Derive
%language ElabReflection

-- An IOArray of exact aent count

-- Not sure how else to extract size while retaining relation without exposing
-- constructor for casing
public export
data SIOArray : Nat -> Type -> Type where
  MkSIOArray : (size : Nat) -> (intSize : Int) -> (content : ArrayData a) -> SIOArray size a

-- I feel like s could allow for easier fusion, by determinig our final size upfront

-- %runElab derive "SIOArray" [Generic,Meta] I can't sop/generic elab this
-- because it doesn't support indexed types that hold the index, e.g. size : Nat
-- above. We'll go to list instead for json.

-- It's time to move to immutable arrays, all this io is gay
-- Your array functions that copy have no reason to be in io

-- 0 so I don't have to remember where to erase it
0 lteReflexive : (j : Nat) -> LTE j j
lteReflexive j = reflexive {x=j}

export
size : SIOArray s a -> Int
size (MkSIOArray s intSize content) = intSize

content : SIOArray s a -> ArrayData a
content (MkSIOArray s intSize c) = c

export
unsafeNewArray : HasIO io => (s : Nat) -> io (SIOArray s a)
unsafeNewArray s = do
  let intsize = cast s
  arr <- primIO (prim__newArray intsize (believe_me (the Int 0)))
  pure (MkSIOArray s intsize arr)

export
newArray : HasIO io => (s : Nat) -> (def : a) -> io (SIOArray s a)
newArray s x = let intsize = cast s
               in pure (MkSIOArray s intsize !(primIO (prim__newArray intsize x)))

export
newArray' : HasIO io => {s:_} -> (def : a) -> io (SIOArray s a)
newArray' x = let intsize = cast s
              in pure (MkSIOArray s intsize !(primIO (prim__newArray intsize x)))

export
newArrayCopy : HasIO io => SIOArray s a -> io (SIOArray s a)
newArrayCopy (MkSIOArray s i contents) = do
    new <- unsafeNewArray s
    copyFrom contents (content new) (i - 1)
    pure new
  where
    copyFrom : ArrayData elem ->
               ArrayData elem ->
               Int -> io ()
    copyFrom old new pos
        = if pos < 0
             then pure ()
             else do el <- primIO $ prim__arrayGet old pos
                     primIO $ prim__arraySet new pos el
                     copyFrom old new $ assert_smaller pos (pos - 1)

export
unsafeMutableWriteArray : HasIO io => SIOArray s a -> (i : Nat) -> a -> io ()
unsafeMutableWriteArray arr i x = primIO (prim__arraySet (content arr) (cast i) x)

export
mutableWriteArray : HasIO io => SIOArray s a -> (i : Nat) -> (0 prf : LTE i s) => a -> io ()
mutableWriteArray arr i x = unsafeMutableWriteArray arr i x

export
||| Don't use this unless you really just have one infrequent thing to change,
||| unsafeWriteArray copies the array every use.
unsafeWriteArray : SIOArray s a -> (i : Nat) -> a -> SIOArray s a
unsafeWriteArray arr i x = unsafePerformIO $ do
  new <- newArrayCopy arr
  unsafeMutableWriteArray new i x
  pure new

export
||| Don't use this unless you really just have one infrequent thing to change,
||| writeArray copies the array every use.
writeArray : SIOArray s a -> (i : Nat) -> (0 prf : LTE i s) => a -> SIOArray s a
writeArray arr i x = unsafeWriteArray arr i x


-- unsafeReadArray doesn't enforce a bounds check

-- primed versions for io ordering/convenience
export
unsafeReadArray' : HasIO io => SIOArray s a -> (i : Nat) -> io a
unsafeReadArray' arr i = primIO (prim__arrayGet (content arr) (cast i))

export
unsafeReadArray : SIOArray s a -> (i : Nat) -> a
unsafeReadArray arr i = unsafePerformIO $ unsafeReadArray' arr i

-- primed versions for io ordering/convenience
export
readArray' : HasIO io => SIOArray s a -> (i : Nat) -> (0 prf : LTE i s) => io a
readArray' arr i = primIO (prim__arrayGet (content arr) (cast i))

export
readArray : SIOArray s a -> (i : Nat) -> (0 prf : LTE i s) => a
readArray arr i = unsafePerformIO $ readArray' arr i

export
modifyArray : HasIO io => (a -> a) -> SIOArray s a -> (i : Nat) -> LTE i s => SIOArray s a
modifyArray f arr i = writeArray arr i (f (readArray arr i))

export
newArrayFillM : HasIO io => (s : Nat) -> (Nat -> io a) -> io (SIOArray s a)
newArrayFillM s g = do
      new <- unsafeNewArray {a} s
      case new of
        MkSIOArray s _ _ => do
          let 0 prf = lteReflexive s
          go new s
          pure new
  where
    go : SIOArray s a -> (i : Nat) -> (0 prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do 
      let 0 newprf = lteSuccLeft prf
      mutableWriteArray new k !(g k)
      go new k

export
foldlArray : HasIO io => (b -> a -> b) -> b -> SIOArray s a -> io b
foldlArray f acc arr = case arr of
    MkSIOArray s _ _ => let 0 prf = lteReflexive s in go s
  where
    go : (i : Nat) -> (0 prf : LTE i s) => io b
    go 0 = pure acc
    go (S k) = let 0 p = lteSuccLeft prf in [| f (go k) (readArray' arr k) |]

export
foldMapArray : (HasIO io, Monoid b) => (a -> b) -> SIOArray s a -> io b
foldMapArray f arr = case arr of
    MkSIOArray s _ _ => let 0 prf = lteReflexive s in go s
  where
    go : (i : Nat) -> (0 prf : LTE i s) => io b
    go 0 = f <$> readArray' arr 0
    go (S k) = let 0 p = lteSuccLeft prf in [| (f <$> readArray' arr k) <+> go k |]

export
mapArray : HasIO io => (a -> b) -> SIOArray s a -> io (SIOArray s b)
mapArray f arr = case arr of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      let 0 prf = lteReflexive s
      go new s
      -- pure new
  where
    go : SIOArray s b -> (i : Nat) -> (0 prf : LTE i s) => io (SIOArray s b)
    go new 0 = pure new
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      v <- readArray' arr k
      mutableWriteArray new k (f v)
      go new k

export
mapArray'' : HasIO io => (a -> b) -> SIOArray s a -> io (SIOArray s b)
mapArray'' f arr1 = case arr1 of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      let 0 prf = lteReflexive s
      go new s
      pure new
  where
    go : SIOArray s b -> (i : Nat) -> (0 prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      v1 <- readArray' arr1 k
      mutableWriteArray new k (f v1)
      go new k

export
mapArray' : (a -> b) -> SIOArray s a -> SIOArray s b
mapArray' f arr = unsafePerformIO $ case arr of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      let 0 prf = lteReflexive s
      go new s
      pure new
  where
    go : SIOArray s b -> (i : Nat) -> (0 prf : LTE i s) => IO ()
    go new 0 = pure ()
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      v <- readArray' arr k
      mutableWriteArray new k (f v)
      go new k

export
Functor (SIOArray s) where
  map = mapArray'

export
imapArrayM : HasIO io => ((i : Nat) -> a -> io b) -> SIOArray s a -> io (SIOArray s b)
imapArrayM f arr = case arr of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      let 0 prf = lteReflexive s
      go new s
      pure new
  where
    go : SIOArray s b -> (i : Nat) -> (0 prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      v <- readArray' arr k
      mutableWriteArray new k !(f k v)
      go new k

export
zipWithArray : HasIO io => (a -> b -> c) -> SIOArray s a -> SIOArray s b -> io (SIOArray s c)
zipWithArray f arr1 arr2 = case arr1 of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=c} s
      let 0 prf = lteReflexive s
      go new s
      pure new
  where
    go : SIOArray s c -> (i : Nat) -> (0 prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      v1 <- readArray' arr1 k
      v2 <- readArray' arr2 k
      mutableWriteArray new k (f v1 v2)
      go new k

export
toList : HasIO io => SIOArray s a -> io (List a)
toList = foldlArray (\b,a => b ++ [a]) []

export
foldlArray' : (b -> a -> b) -> b -> SIOArray s a -> b
foldlArray' f acc arr = case arr of
    MkSIOArray s _ _ => let 0 prf = lteReflexive s in go s
  where
    go : (i : Nat) -> (0 prf : LTE i s) => b
    go 0 = acc
    go (S k) = let 0 p = lteSuccLeft prf in f (go k) (readArray arr k)

export
toList' : SIOArray s a -> List a
toList' xs = foldlArray' (\b,a => b . (a ::)) id xs []

export
fromList : HasIO io => (xs : List a) -> io (SIOArray (length xs) a)
fromList xs with (length xs)
  fromList xs | s = do
      new <- unsafeNewArray {a} s
      let 0 prf = lteReflexive s
      go new (reverse xs) s
      pure new
  where
    go : SIOArray s a -> (xs : List a) -> (i : Nat) -> (0 prf : LTE i s) => io ()
    go new (x :: xs) (S k) = do
      let 0 newprf = lteSuccLeft prf
      mutableWriteArray new k x
      go new xs k
    go new _ _ = pure ()

-- the length + reversing is slowish, merge the op? build up a chain of writes to execute after length is known?
export
fromList' : HasIO io => (xs : List a) -> io (s : Nat ** SIOArray s a)
fromList' xs = do
    let s = length xs
    new <- unsafeNewArray {a} s
    let 0 prf = lteReflexive s
    go new (reverse xs) s
    pure (s ** new)
  where
    go : SIOArray s a -> (xs : List a) -> (i : Nat) -> (0 prf : LTE i s) => io ()
    go new (x :: xs) (S k) = do
      let 0 newprf = lteSuccLeft prf
      mutableWriteArray new k x
      go new xs k
    go new _ _ = pure ()

-- the length + reversing is slowish, merge the op? build up a chain of writes to execute after length is known?
export
fromList'' : (xs : List a) -> (s : Nat ** SIOArray s a)
fromList'' xs = unsafePerformIO $ fromList' xs

export
fromList''' : (xs : List a) -> SIOArray (length xs) a
fromList''' xs = unsafePerformIO $ fromList xs

export
prettyArray : Show a => SIOArray s a -> String
prettyArray x = show (toList' x)

export
Show a => Show (SIOArray s a) where
  show x = "fromList " ++ prettyArray x

export
%inline
pointwise' : HasIO io => Num a => SIOArray s (a -> b) -> SIOArray s a -> io (SIOArray s b)
pointwise' = zipWithArray (\f,x => f x)

export
%inline
pointwise : HasIO io => Num a => SIOArray s a -> SIOArray s a -> io (SIOArray s a)
pointwise = zipWithArray (+)

export
%inline
(+) : HasIO io => Num a => SIOArray s a -> SIOArray s a -> io (SIOArray s a)
(+) = pointwise

export
arrEq : HasIO io => Eq a => SIOArray s a -> SIOArray s a -> io Bool
arrEq x y = foldlArray (&&|) True =<< zipWithArray (==) x y

export
sumArray : HasIO io => Num a => SIOArray s a -> io a
sumArray = foldlArray (+) 0

export
dotArray : HasIO io => Num a => SIOArray s a -> SIOArray s a -> io a
dotArray a b = sumArray !(zipWithArray (*) a b)


export
ToJSON a => ToJSON (SIOArray s a) where
  toJSON = toJSON . toList'

export
FromJSON a => FromJSON (s : Nat ** SIOArray s a) where
  fromJSON = map fromList'' . fromJSON

export
{s:_} -> FromJSON a => FromJSON (SIOArray s a) where
  fromJSON x = do
    xs <- fromJSON {a=List a} x
    case decEq (length xs) s of
      (No contra) => fail "List length not correct, expected \{show s} got \{show (length xs)}"
      (Yes Refl) => Right $ fromList''' xs
    





----------- Not worth the work

-- Forcing particular operations into interfaces makes over-restrictive
-- functions, e.g. fromInteger forces us to create a specific array, requiring
-- us to know what 's' is, but + and * don't need this restriction since zipWith
-- rediscovers what s was via pattern matching. Hence we provide the operations
-- below without an accompanying interface.
-- 
-- ----------- Num
-- 
-- -- export
-- (+) : Num a => SIOArray s a -> SIOArray s a -> SIOArray s a
-- x + y = unsafePerformIO $ zipWithArray (+) x y
-- 
-- -- export
-- (*) : Num a => SIOArray s a -> SIOArray s a -> SIOArray s a
-- x * y = unsafePerformIO $ zipWithArray (*) x y
-- 
-- -- export
-- fromInteger : Num a => (s:_) => Integer -> SIOArray s a
-- -- fromInteger x = unsafePerformIO $ newArray' (fromInteger x)
-- fromInteger x = unsafePerformIO $ newArray' (fromInteger x)
-- 
-- Num a => (s : Nat) => Num (SIOArray s a) where
--  (*) = IOArray.(*)
--  (+) = IOArray.(+)
--  fromInteger x = unsafePerformIO $ newArray' (fromInteger x)
-- 
-- ----------- Fractional
-- 
-- export
-- (/) : Fractional a => SIOArray s a -> SIOArray s a -> SIOArray s a
-- x / y = unsafePerformIO $ zipWithArray (/) x y
-- -- recip : Fractional a => SIOArray s a -> SIOArray s a
-- 
-- ----------- FromDouble
-- 
-- export
-- fromDouble : FromDouble a => {s:_} -> a -> SIOArray s a
-- fromDouble x = ?dfsdsdds --unsafePerformIO $ newArray' (fromDouble x)
-- 
-- ----------- Neg
-- 
-- export
-- negate : Neg a => SIOArray s a -> SIOArray s a
-- negate x = unsafePerformIO $ mapArray negate x
-- (-) : Neg a => SIOArray s a -> SIOArray s a -> SIOArray s a
-- x - y = unsafePerformIO $ zipWithArray (-) x y
-- 
-- ----------- Floating
-- 
-- Floating a => Floating (SIOArray s a) where
--   exp x = unsafePerformIO $ mapArray exp x
--   pi = ?fsfsd
--   euler = ?fsdfddds
--   log x = ?ffefsdf324sefsefsefsdfsfsf
--   pow x y = ?ffefs2534dfsefsefsefsdfsfsf
--   sin x = ?ffefsdfsefsefsef34543sdfsfsf
--   cos x = ?ffefsd3453fsefsefsefsdfsfsf
--   tan x = ?ffefsdfsefs345efsefsdfsfsf
--   asin x = ?ffefsdfsefsefs123123efsdfsfsf
--   acos x = ?ffefs123dfsefsefsefsdfsfsf
--   atan x = ?ffefsd34534fsefsefsefsdfsfsf
--   sinh x = ?ffefsdfsef32432sefsefsdfsfsf
--   cosh x = ?ffefsdfsefsefsefsdfs5645fsf
--   tanh x = ?ffefsdfsefse45654654fsefsdfsfsf
--   sqrt x = ?ffe45654fsdfsefsefsefsdfsfsf
--   floor x = ?ffefsdfse12312fsefsefsdfsfsf
--   ceiling x = ?ffefsdfsefsefsefs1312dfsfsf
-- 
-- 
-- 
-- -- 
-- -- export
-- -- pi : FromDouble a => {s:_} -> SIOArray s a
-- -- pi = unsafePerformIO $ newArray' (fromDouble 3.14159265358979323846)
-- -- 
-- -- export
-- -- euler : FromDouble a => {s:_} -> SIOArray s a
-- -- euler = unsafePerformIO $ newArray' (fromDouble 2.7182818284590452354)
-- -- 
-- -- export
-- -- exp : Floating a => SIOArray s a -> SIOArray s a
-- -- exp x = unsafePerformIO $ mapArray exp x
-- -- 
-- -- export
-- -- log : Floating a => SIOArray s a -> SIOArray s a
-- -- log x = unsafePerformIO $ mapArray log x
-- -- 
-- -- export
-- -- pow : Floating a => SIOArray s a -> SIOArray s a -> SIOArray s a
-- -- pow x y = unsafePerformIO $ zipWithArray pow x y
-- -- 
-- -- export
-- -- sin : Floating a => SIOArray s a -> SIOArray s a
-- -- sin x = unsafePerformIO $ mapArray sin x
-- -- 
-- -- export
-- -- cos : Floating a => SIOArray s a -> SIOArray s a
-- -- cos x = unsafePerformIO $ mapArray cos x
-- -- 
-- -- export
-- -- tan : Floating a => SIOArray s a -> SIOArray s a
-- -- tan x = unsafePerformIO $ mapArray tan x
-- -- 
-- -- export
-- -- asin : Floating a => SIOArray s a -> SIOArray s a
-- -- asin x = unsafePerformIO $ mapArray asin x
-- -- 
-- -- export
-- -- acos : Floating a => SIOArray s a -> SIOArray s a
-- -- acos x = unsafePerformIO $ mapArray acos x
-- -- 
-- -- export
-- -- atan : Floating a => SIOArray s a -> SIOArray s a
-- -- atan x = unsafePerformIO $ mapArray atan x
-- -- 
-- -- export
-- -- sinh : Floating a => SIOArray s a -> SIOArray s a
-- -- sinh x = unsafePerformIO $ mapArray sinh x
-- -- 
-- -- export
-- -- cosh : Floating a => SIOArray s a -> SIOArray s a
-- -- cosh x = unsafePerformIO $ mapArray cosh x
-- -- 
-- -- export
-- -- tanh : Floating a => SIOArray s a -> SIOArray s a
-- -- tanh x = unsafePerformIO $ mapArray tanh x
-- -- 
-- -- export
-- -- sqrt : Floating a => SIOArray s a -> SIOArray s a
-- -- sqrt x = unsafePerformIO $ mapArray sqrt x
-- -- 
-- -- export
-- -- floor : Floating a => SIOArray s a -> SIOArray s a
-- -- floor x = unsafePerformIO $ mapArray floor x
-- -- 
-- -- export
-- -- ceiling : Floating a => SIOArray s a -> SIOArray s a
-- -- ceiling x = unsafePerformIO $ mapArray ceiling x
