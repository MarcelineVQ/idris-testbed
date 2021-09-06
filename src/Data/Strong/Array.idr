module Data.Strong.Array

import Data.IOArray.Prims
import Data.Fin
import public Data.Nat
import Data.DPair

import Control.Monad.Identity

import Num.Floating

import Data.List

import System.Random

import Decidable.Equality
import JSON
import Generics.Derive
%language ElabReflection

-- An IOArray of exact aent count

-- Not sure how else to extract size while retaining relation without exposing
-- constructor for casing
public export
data Array : Nat -> Type -> Type where
  MkArray : (size : Nat) -> (intSize : Int) -> (content : ArrayData a) -> Array size a

-- I feel like s could allow for eason fusion, by determinig our final size upfront

-- %runElab derive "Array" [Generic,Meta] I can't sop/generic elab this
-- because it doesn't support indexed types that hold the index, e.g. size : Nat
-- above. We'll go to list instead for json.

-- It's time to move to immutable arrays, all this io is gay
-- Your array functions that copy have no reason to be in io

-- 0 so I don't have to remember where to erase it
0 lteReflexive : (j : Nat) -> LTE j j
lteReflexive j = reflexive {x=j}

export
size : Array s a -> Int
size (MkArray s intSize content) = intSize

content : Array s a -> ArrayData a
content (MkArray s intSize c) = c

export
newArray : (s : Nat) -> (def : a) -> Array s a
newArray s x = unsafePerformIO $ do
    let intsize = cast s
    pure (MkArray s intsize !(primIO (prim__newArray intsize x)))

export
newArray' : {s:_} -> (def : a) -> Array s a
newArray' = newArray s

export
newUnintializedArray : (s : Nat) -> Array s a
newUnintializedArray s = newArray s (believe_me (the Int 0))

export
newUnintializedArray' : {s : Nat} -> Array s a
newUnintializedArray' = newUnintializedArray s

export
newArrayCopy : Array s a -> Array s a
newArrayCopy (MkArray s i contents) = unsafePerformIO $ do
    let new = newUnintializedArray s
    copyFrom contents (content new) (i - 1)
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
unsafeMutableWriteArray : HasIO io => Array s a -> (i : Nat) -> a -> io ()
unsafeMutableWriteArray arr i x = primIO (prim__arraySet (content arr) (cast i) x)

export
mutableWriteArray : HasIO io => Array s a -> (i : Nat) -> (0 prf : LTE i s) => a -> io ()
mutableWriteArray arr i x = unsafeMutableWriteArray arr i x

export
||| Don't use this unless you really just have one infrequent thing to change,
||| unsafeWriteArray copies the array every use.
unsafeWriteArray : Array s a -> (i : Nat) -> a -> Array s a
unsafeWriteArray arr i x = unsafePerformIO $ do
  let new = newArrayCopy arr
  unsafeMutableWriteArray new i x
  pure new

export
||| Don't use this unless you really just have one infrequent thing to change,
||| writeArray copies the array every use.
writeArray : Array s a -> (i : Nat) -> (0 prf : LTE i s) => a -> Array s a
writeArray arr i x = unsafeWriteArray arr i x


-- unsafeReadArray doesn't enforce a bounds check

export
||| To match with unsafeMutableWriteArray in that it has io for
||| ordering ease-of-use, 'mutable' in name only.
unsafeMutableReadArray : HasIO io => Array s a -> (i : Nat) -> io a
unsafeMutableReadArray arr i = primIO (prim__arrayGet (content arr) (cast i))

export
unsafeReadArray : Array s a -> (i : Nat) -> a
unsafeReadArray arr i = unsafePerformIO $ unsafeMutableReadArray arr i

export
||| To match with unsafeMutableWriteArray in that it has io for
||| ordering ease-of-use, 'mutable' in name only.
mutableReadArray : HasIO io => Array s a -> (i : Nat) -> (0 prf : LTE i s) => io a
mutableReadArray arr i = unsafeMutableReadArray arr i

export
readArray : Array s a -> (i : Nat) -> (0 prf : LTE i s) => a
readArray arr i = unsafeReadArray arr i

export
modifyArray : (a -> a) -> Array s a -> (i : Nat) -> LTE i s => Array s a
modifyArray f arr i = writeArray arr i (f (readArray arr i))

export
imapArrayM : Monad m => ((i : Nat) -> a -> m b) -> Array s a -> m (Array s b)
imapArrayM f arr = case arr of
    MkArray s _ _ => do
      let new = newUnintializedArray {a=b} s
      let 0 prf = lteReflexive s
      go new s
  where
    go : Array s b -> (i : Nat) -> (0 prf : LTE i s) => m (Array s b)
    go new 0 = pure new
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      let v = readArray arr k
      r <- f k v
      let () = unsafePerformIO $ mutableWriteArray new k r
      go new k

export
imapArray : ((i : Nat) -> a -> b) -> Array s a -> Array s b
imapArray f arr = runIdentity $ imapArrayM (Id .: f) arr


-- extra copy, but easy to write
export
inewArrayFillM : Monad m => (s : Nat) -> ((i : Nat) -> m a) -> m (Array s a)
inewArrayFillM s g = imapArrayM (\i,_ => g i) (newUnintializedArray {a} s)

export
inewArrayFill : (s : Nat) -> ((i : Nat) -> a) -> Array s a
inewArrayFill s g = runIdentity $ imapArrayM (\i,_ => Id (g i)) (newUnintializedArray {a} s)


export
foldlArray : (b -> a -> b) -> b -> Array s a -> b
foldlArray f acc arr = unsafePerformIO $ case arr of
    MkArray s _ _ => let 0 prf = lteReflexive s in go s
  where
    go : (i : Nat) -> (0 prf : LTE i s) => IO b
    go 0 = pure acc
    go (S k) = let 0 p = lteSuccLeft prf in [| f (go k) (mutableReadArray arr k) |]

-- export
-- foldMapArray : (HasIO io, Monoid b) => (a -> b) -> Array s a -> io b
-- foldMapArray f arr = case arr of
--     MkArray s _ _ => let 0 prf = lteReflexive s in go s
--   where
--     go : (i : Nat) -> (0 prf : LTE i s) => io b
--     go 0 = f <$> readArray' arr 0
--     go (S k) = let 0 p = lteSuccLeft prf in [| (f <$> readArray' arr k) <+> go k |]

export
mapArray : (a -> b) -> Array s a -> Array s b
mapArray f arr = imapArray (\_,x => f x) arr

export
zipWithArray : (a -> b -> c) -> Array s a -> Array s b -> Array s c
zipWithArray f arr1 arr2 = unsafePerformIO $ case arr1 of
    MkArray s _ _ => do
      let new = newUnintializedArray {a=c} s
      let 0 prf = lteReflexive s
      go new s
      pure new
  where
    go : Array s c -> (i : Nat) -> (0 prf : LTE i s) => IO ()
    go new 0 = pure ()
    go new (S k) = do
      let 0 newprf = lteSuccLeft prf
      v1 <- mutableReadArray arr1 k
      v2 <- mutableReadArray arr2 k
      mutableWriteArray new k (f v1 v2)
      go new k

export
Functor (Array s) where
  map = mapArray

export
{s:_} -> Applicative (Array s) where
  pure a = newArray' a
  f <*> fa = zipWithArray (\f,x => f x) f fa

export
toList : Array s a -> List a
toList xs = foldlArray (\b,a => b . (a ::)) id xs []

export
fromList : (xs : List a) -> Array (length xs) a
fromList xs with (length xs)
  fromList xs | s = unsafePerformIO $ do
      let new = newUnintializedArray {a} s
      let 0 prf = lteReflexive s
      go new (reverse xs) s
      pure new
  where
    go : Array s a -> (xs : List a) -> (i : Nat) -> (0 prf : LTE i s) => IO ()
    go new (x :: xs) (S k) = do
      let 0 newprf = lteSuccLeft prf
      mutableWriteArray new k x
      go new xs k
    go new _ _ = pure ()

-- the length + reversing is slowish, merge the op? build up a chain of writes to execute after length is known?
export
fromList' : (xs : List a) -> (s : Nat ** Array s a)
fromList' xs = unsafePerformIO $ do
    let s = length xs
    let new = newUnintializedArray {a} s
    let 0 prf = lteReflexive s
    go new (reverse xs) s
    pure (s ** new)
  where
    go : Array s a -> (xs : List a) -> (i : Nat) -> (0 prf : LTE i s) => IO ()
    go new (x :: xs) (S k) = do
      let 0 newprf = lteSuccLeft prf
      mutableWriteArray new k x
      go new xs k
    go new _ _ = pure ()

export
Show a => Show (Array s a) where
  show x = "fromList " ++ show (Array.toList x)

export
%inline
pointwise : Num a => Array s a -> Array s a -> Array s a
pointwise = zipWithArray (+)

export
%inline
(+) : Num a => Array s a -> Array s a -> Array s a
(+) = pointwise

export
sumArray : Num a => Array s a -> a
sumArray = foldlArray (+) 0

export
dotArray : Num a => Array s a -> Array s a -> a
dotArray a b = sumArray (zipWithArray (*) a b)


export
ToJSON a => ToJSON (Array s a) where
  toJSON = toJSON . Array.toList

export
FromJSON a => FromJSON (s : Nat ** Array s a) where
  fromJSON = map fromList' . fromJSON

export
{s:_} -> FromJSON a => FromJSON (Array s a) where
  fromJSON x = do
    xs <- fromJSON {a=List a} x
    case decEq (length xs) s of
      (No contra) => fail "List length not correct, expected \{show s} got \{show (length xs)}"
      (Yes Refl) => Right $ fromList xs




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
-- (+) : Num a => Array s a -> Array s a -> Array s a
-- x + y = unsafePerformIO $ zipWithArray (+) x y
-- 
-- -- export
-- (*) : Num a => Array s a -> Array s a -> Array s a
-- x * y = unsafePerformIO $ zipWithArray (*) x y
-- 
-- -- export
-- fromInteger : Num a => (s:_) => Integer -> Array s a
-- -- fromInteger x = unsafePerformIO $ newArray' (fromInteger x)
-- fromInteger x = unsafePerformIO $ newArray' (fromInteger x)
-- 
-- Num a => (s : Nat) => Num (Array s a) where
--  (*) = IOArray.(*)
--  (+) = IOArray.(+)
--  fromInteger x = unsafePerformIO $ newArray' (fromInteger x)
-- 
-- ----------- Fractional
-- 
-- export
-- (/) : Fractional a => Array s a -> Array s a -> Array s a
-- x / y = unsafePerformIO $ zipWithArray (/) x y
-- -- recip : Fractional a => Array s a -> Array s a
-- 
-- ----------- FromDouble
-- 
-- export
-- fromDouble : FromDouble a => {s:_} -> a -> Array s a
-- fromDouble x = ?dfsdsdds --unsafePerformIO $ newArray' (fromDouble x)
-- 
-- ----------- Neg
-- 
-- export
-- negate : Neg a => Array s a -> Array s a
-- negate x = unsafePerformIO $ mapArray negate x
-- (-) : Neg a => Array s a -> Array s a -> Array s a
-- x - y = unsafePerformIO $ zipWithArray (-) x y
-- 
-- ----------- Floating
-- 
-- Floating a => Floating (Array s a) where
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
-- -- pi : FromDouble a => {s:_} -> Array s a
-- -- pi = unsafePerformIO $ newArray' (fromDouble 3.14159265358979323846)
-- -- 
-- -- export
-- -- euler : FromDouble a => {s:_} -> Array s a
-- -- euler = unsafePerformIO $ newArray' (fromDouble 2.7182818284590452354)
-- -- 
-- -- export
-- -- exp : Floating a => Array s a -> Array s a
-- -- exp x = unsafePerformIO $ mapArray exp x
-- -- 
-- -- export
-- -- log : Floating a => Array s a -> Array s a
-- -- log x = unsafePerformIO $ mapArray log x
-- -- 
-- -- export
-- -- pow : Floating a => Array s a -> Array s a -> Array s a
-- -- pow x y = unsafePerformIO $ zipWithArray pow x y
-- -- 
-- -- export
-- -- sin : Floating a => Array s a -> Array s a
-- -- sin x = unsafePerformIO $ mapArray sin x
-- -- 
-- -- export
-- -- cos : Floating a => Array s a -> Array s a
-- -- cos x = unsafePerformIO $ mapArray cos x
-- -- 
-- -- export
-- -- tan : Floating a => Array s a -> Array s a
-- -- tan x = unsafePerformIO $ mapArray tan x
-- -- 
-- -- export
-- -- asin : Floating a => Array s a -> Array s a
-- -- asin x = unsafePerformIO $ mapArray asin x
-- -- 
-- -- export
-- -- acos : Floating a => Array s a -> Array s a
-- -- acos x = unsafePerformIO $ mapArray acos x
-- -- 
-- -- export
-- -- atan : Floating a => Array s a -> Array s a
-- -- atan x = unsafePerformIO $ mapArray atan x
-- -- 
-- -- export
-- -- sinh : Floating a => Array s a -> Array s a
-- -- sinh x = unsafePerformIO $ mapArray sinh x
-- -- 
-- -- export
-- -- cosh : Floating a => Array s a -> Array s a
-- -- cosh x = unsafePerformIO $ mapArray cosh x
-- -- 
-- -- export
-- -- tanh : Floating a => Array s a -> Array s a
-- -- tanh x = unsafePerformIO $ mapArray tanh x
-- -- 
-- -- export
-- -- sqrt : Floating a => Array s a -> Array s a
-- -- sqrt x = unsafePerformIO $ mapArray sqrt x
-- -- 
-- -- export
-- -- floor : Floating a => Array s a -> Array s a
-- -- floor x = unsafePerformIO $ mapArray floor x
-- -- 
-- -- export
-- -- ceiling : Floating a => Array s a -> Array s a
-- -- ceiling x = unsafePerformIO $ mapArray ceiling x
