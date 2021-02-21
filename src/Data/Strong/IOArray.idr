module Data.Strong.IOArray

import Data.IOArray.Prims
import Data.Fin
import public Data.Nat
import Data.DPair

import Num.Floating

import Data.List

-- An IOArray of exact aent count

-- Not sure how else to extract size while retaining relation without exposing
-- constructor for casing
public export
data SIOArray : (size : Nat) -> Type -> Type where
  MkSIOArray : (size : Nat) -> (intSize : Int) -> (content : ArrayData a) -> SIOArray size a

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
writeArray : HasIO io => SIOArray s a -> (i : Nat) -> (prf : LTE i s) => a -> io ()
writeArray arr i x = primIO (prim__arraySet (content arr) (cast i) x)

export
readArray : HasIO io => SIOArray s a -> (i : Nat) -> (prf : LTE i s) => io a
readArray arr i = primIO (prim__arrayGet (content arr) (cast i))

export
readArray' : HasIO io => SIOArray s a -> (i : Nat) -> (prf : LTE i s) => io a
readArray' arr i = primIO (prim__arrayGet (content arr) (cast i))

export
modifyArray : HasIO io => (a -> a) -> SIOArray s a -> (i : Nat) -> LTE i s => io ()
modifyArray f arr i = do
  v <- readArray arr i
  writeArray arr i (f v)

fef : (j : Nat) -> LTE j j
fef 0 = LTEZero
fef (S k) = LTESucc (fef k)

export
newArrayFillM : HasIO io => (s : Nat) -> (Nat -> io a) -> io (SIOArray s a)
newArrayFillM s g = do
      new <- unsafeNewArray {a} s
      case new of
        MkSIOArray s _ _ => do
          go new s {prf = fef s}
          pure new
  where
    go : SIOArray s a -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do 
      let newprf = lteSuccLeft prf
      writeArray new k !(g k)
      go new k

export
foldlArray : HasIO io => (b -> a -> b) -> b -> SIOArray s a -> io b
foldlArray f acc arr = case arr of
    MkSIOArray s _ _ => go s {prf = fef s}
  where
    go : (i : Nat) -> (prf : LTE i s) => io b
    go 0 = pure acc
    go (S k) = let p = lteSuccLeft prf in [| f (go k) (readArray arr k) |]

export
foldMapArray : (HasIO io, Monoid b) => (a -> b) -> SIOArray s a -> io b
foldMapArray f arr = case arr of
    MkSIOArray s _ _ => go s {prf = fef s}
  where
    go : (i : Nat) -> (prf : LTE i s) => io b
    go 0 = f <$> readArray arr 0
    go (S k) = let p = lteSuccLeft prf in [| (f <$> readArray arr k) <+> go k |]

export
mapArray : HasIO io => (a -> b) -> SIOArray s a -> io (SIOArray s b)
mapArray f arr = case arr of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      go new s {prf = fef s}
      pure new
  where
    go : SIOArray s b -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do
      let newprf = lteSuccLeft prf
      v <- readArray arr k
      writeArray new k (f v)
      go new k

export
imapArrayM : HasIO io => ((i : Nat) -> a -> io b) -> SIOArray s a -> io (SIOArray s b)
imapArrayM f arr = case arr of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=b} s
      go new s {prf = fef s}
      pure new
  where
    go : SIOArray s b -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do
      let newprf = lteSuccLeft prf
      v <- readArray arr k
      writeArray new k !(f k v)
      go new k

export
zipWithArray : HasIO io => (a -> b -> c) -> SIOArray s a -> SIOArray s b -> io (SIOArray s c)
zipWithArray f arr1 arr2 = case arr1 of
    MkSIOArray s _ _ => do
      new <- unsafeNewArray {a=c} s
      go new s {prf = fef s}
      pure new
  where
    go : SIOArray s c -> (i : Nat) -> (prf : LTE i s) => io ()
    go new 0 = pure ()
    go new (S k) = do
      let newprf = lteSuccLeft prf
      v1 <- readArray arr1 k
      v2 <- readArray arr2 k
      writeArray new k (f v1 v2)
      go new k

export
toList : HasIO io => SIOArray s a -> io (List a)
toList = foldlArray (\b,a => b ++ [a]) []

export
fromList : HasIO io => (xs : List a) -> io (SIOArray (length xs) a)
fromList xs with (length xs)
  fromList xs | s = do
      new <- unsafeNewArray {a} s
      go new (reverse xs) s {prf = fef s}
      pure new
  where
    go : SIOArray s a -> (xs : List a) -> (i : Nat) -> (prf : LTE i s) => io ()
    go new (x :: xs) (S k) = do
      let newprf = lteSuccLeft prf
      writeArray new k x
      go new xs k
    go new _ _ = pure ()

export
fromList' : HasIO io => (xs : List a) -> io (s : Nat ** SIOArray s a)
fromList' xs = do
    let s = length xs
    new <- unsafeNewArray {a} s
    go new (reverse xs) s {prf = fef s}
    pure (s ** new)
  where
    go : SIOArray s a -> (xs : List a) -> (i : Nat) -> (prf : LTE i s) => io ()
    go new (x :: xs) (S k) = do
      let newprf = lteSuccLeft prf
      writeArray new k x
      go new xs k
    go new _ _ = pure ()

export
prettyArray : Show a => SIOArray s a -> String
prettyArray x = show (unsafePerformIO $ toList x)

export
Show a => Show (SIOArray s a) where
  show x = "fromList " ++ prettyArray x

export
%inline
pointwise : HasIO io => Num a => SIOArray s a -> SIOArray s a -> io (SIOArray s a)
pointwise = zipWithArray (+)

export
%inline
(+) : HasIO io => Num a => SIOArray s a -> SIOArray s a -> io (SIOArray s a)
(+) = pointwise

export
sumArray : HasIO io => Num a => SIOArray s a -> io a
sumArray = foldlArray (+) 0

export
dotArray : HasIO io => Num a => {s:_} -> SIOArray s a -> SIOArray s a -> io a
dotArray a b = sumArray =<< zipWithArray (*) a b







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
