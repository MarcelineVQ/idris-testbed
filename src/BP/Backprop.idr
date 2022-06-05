module BP.Backprop

import Numeric.Floating

import Control.Monad.Trans
import public Control.Monad.ST
import public Control.Monad.Cont

import Control.Monad.Identity

-- import Data.Strong.Array

import Data.List

import Util

import Generics.Newtype
%language ElabReflection

public export
record D a where
  constructor MkD
  primal : a
  dual : Lazy a

export
Show a => Show (D a) where
  showPrec prec (MkD p d) = showCon prec "D" $ showArg p ++ showArg d

export %inline
mapPrimal : (a -> a) -> D a -> D a
mapPrimal f (MkD x y) = MkD (f x) y

export %inline
mapDual : (a -> a) -> D a -> D a
mapDual f (MkD x y) = MkD x (f y)

export
Eq a => Eq (D a) where
  MkD x _ == MkD y _ = x == y

export
Ord a => Ord (D a) where
  compare (MkD x _) (MkD y _) = compare x y

public export
DVar : (s : Type) -> (a : Type) ->  Type
DVar s a = STRef s (D a)

export
var : a -> a -> ST s (DVar s a)
var x dx = newSTRef (MkD x dx)

public export
record AD0 s a where
  constructor MkAD0
  unAD0 : forall x . ContT x (ST s) a

export
Functor (AD0 s) where
    map f (MkAD0 x) = MkAD0 $ map f x

export
Applicative (AD0 s) where
  pure a = MkAD0 $ pure a
  MkAD0 f <*> MkAD0 fa = MkAD0 $ f <*> fa

public export
AD : Type -> Type -> Type
AD s a = AD0 s (DVar s a)


-- | 'zero' for instances of 'Num'. lazy in its argument.
export %inline
zeroNum : Num a => a -> a
zeroNum _ = 0

-- | 'add' for instances of 'Num'.
export %inline
addNum : Num a => a -> a -> a
addNum = (+)

-- | 'one' for instances of 'Num'. lazy in its argument.
export %inline
oneNum : Num a => a -> a
oneNum _ = 1


public export
interface Backprop a where
  constructor MkBackprop
  zero : a -> a
  one : a -> a
  add : a -> a -> a

export %inline
auto' : a -> AD s a
auto' x = MkAD0 $ lift $ var x (lie_idris_crash "auto' zero was forced")
-- auto' x = MkAD0 $ lift $ var x (zero x)
-- auto' x = MkAD0 $ lift $ var x (believe_me 0)

export %inline
auto'' : Num a => a -> AD s a
auto'' x = MkAD0 $ lift $ var x 0

-- giving this to every `Num a` can cause interface conflicts
export
[DefaultNumBackprop]
Num a => Backprop a where
  zero = zeroNum
  one = oneNum
  add = addNum

export
Backprop Double where
  zero = zeroNum
  one = oneNum
  add = addNum

export
Backprop Int where
  zero = zeroNum
  one = oneNum
  add = addNum

export
Backprop Integer where
  zero = zeroNum
  one = oneNum
  add = addNum

-- | Lift a unary function
-- This is a polymorphic combinator for tracking how primal and adjoint values are transformed by a function.
-- How does this work :
-- 1) Compute the function result and bind the function inputs to the adjoint updating function (the "pullback")
-- 2) Allocate a fresh STRef @rb@ with the function result and @zero@ adjoint part
-- 3) @rb@ is passed downstream as an argument to the continuation @k@, with the expectation that the STRef will be mutated
-- 4) Upon returning from the @k@ (bouncing from the boundary of @resetT@), the mutated STRef is read back in
-- 5) The adjoint part of the input variable is updated using @rb@ and the result of the continuation is returned.
export %inline
op1_  : Show a
     => (b -> b) -- ^ zero
     -> (a -> a -> a) -- ^ plus
     -> (a -> (b, b -> a)) -- ^ returns : (function result, pullback)
     -> ContT x (ST s) (DVar s a)
     -> ContT x (ST s) (DVar s b)
op1_ zeroa plusa f ioa = do
  ra <- ioa
  (MkD xa _) <- lift $ readSTRef ra
  let (xb, g) = f xa -- 1)
  shiftT $ \k => lift $ do
    rb <- var xb (zeroa xb) -- 2)
    ry <- k rb -- 3)
    (MkD _ yd) <- readSTRef rb -- 4)
    modifySTRef ra (mapDual (\rda0 => rda0 `plusa` g yd)) -- 5)
    -- pure $ unsafePerformIO $ putStrLn $ "rda_op1_: " ++ show !(readSTRef ra)
    pure ry

-- | Lift a unary function
-- The first two arguments constrain the types of the adjoint values of the
-- output and input variable respectively, see 'op1Num' for an example.
-- The third argument is the most interesting: it specifies at once how to
-- compute the function value and how to compute the sensitivity with respect to
-- the function parameter.
-- Note: the type parameters are completely unconstrained.
export %inline
op1  : Show a
    => (b -> b) -- ^ zero
    -> (a -> a -> a) -- ^ plus
    -> (a -> (b, b -> a)) -- ^ returns : (function result, pullback)
    -> AD s a
    -> AD s b
op1 z plusa f (MkAD0 ioa) = MkAD0 $ op1_ z plusa f ioa

export %inline
op1'  : Show a => Backprop a => Backprop b
    => (a -> (b, b -> a))
    -> AD s a
    -> AD s b
op1' f (MkAD0 ioa) = MkAD0 $ op1_ zero add f ioa


-- | Helper for constructing unary functions that operate on Num instances (i.e. 'op1' specialized to Num)
export %inline
op1Num  : Show a => (Num a, Num b) =>
          (a -> (b, b -> a)) -- ^ returns : (function result, pullback)
       -> AD s a
       -> AD s b
op1Num = op1 zeroNum addNum

-- | Lift a binary function
export %inline
op2_  : Show a => Show b => Show c
     => c -- ^ zero
     -> (a -> a -> a) -- ^ plus
     -> (b -> b -> b) -- ^ plus
     -> (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullbacks)
     -> ContT x (ST s) (DVar s a)
     -> ContT x (ST s) (DVar s b)
     -> ContT x (ST s) (DVar s c)
op2_ zeroa plusa plusb f ioa iob = do
  ra <- ioa
  rb <- iob
  (MkD xa _) <- lift $ readSTRef ra
  (MkD xb _) <- lift $ readSTRef rb
  let (xc, g, h) = f xa xb
  shiftT $ \k => lift $ do
    rc <- var xc zeroa
    ry <- k rc
    (MkD _ yd) <- readSTRef rc
    modifySTRef ra (mapDual (\rda0 => rda0 `plusa` g yd))
    modifySTRef rb (mapDual (\rdb0 => rdb0 `plusb` h yd))
    -- pure $ unsafePerformIO $ putStrLn $ "rda_op2_: " ++ show !(readSTRef ra)
    -- pure $ unsafePerformIO $ putStrLn $ "rdb_op2_: " ++ show !(readSTRef rb)
    pure ry

-- | Lift a binary function
--
-- See 'op1' for more information.
export %inline
op2  : Show a => Show b => Show c
    => c -- ^ zero
    -> (a -> a -> a) -- ^ plus
    -> (b -> b -> b) -- ^ plus
    -> (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullbacks)
    -> (AD s a -> AD s b -> AD s c)
op2 z plusa plusb f (MkAD0 ioa) (MkAD0 iob) = MkAD0 $ op2_ z plusa plusb f ioa iob

export %inline
op2'_ : Show a => Show b => Show c
     => (c -> c) -- ^ zero
     -> (a -> a -> a) -- ^ plus
     -> (b -> b -> b) -- ^ plus
     -> (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullbacks)
     -> ContT x (ST s) (DVar s a)
     -> ContT x (ST s) (DVar s b)
     -> ContT x (ST s) (DVar s c)
op2'_ zeroa plusa plusb f ioa iob = do
  ra <- ioa
  rb <- iob
  (MkD xa _) <- lift $ readSTRef ra
  (MkD xb _) <- lift $ readSTRef rb
  let (xc, g, h) = f xa xb
  shiftT $ \k => lift $ do
    rc <- var xc (zeroa xc)
    ry <- k rc
    (MkD _ yd) <- readSTRef rc
    modifySTRef ra (mapDual (\rda0 => rda0 `plusa` g yd))
    modifySTRef rb (mapDual (\rdb0 => rdb0 `plusb` h yd))
    -- pure $ unsafePerformIO $ putStrLn $ "rda_op2'_: " ++ show !(readSTRef ra)
    -- pure $ unsafePerformIO $ putStrLn $ "rdb_op2'_: " ++ show !(readSTRef rb)
    pure ry

export %inline
op2'  : Backprop a => Backprop b => Backprop c => Show a => Show b => Show c
    => (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullbacks)
    -> (AD s a -> AD s b -> AD s c)
op2' f (MkAD0 ioa) (MkAD0 iob) = MkAD0 $ op2'_ zero add add f ioa iob

-- | Helper for constructing binary functions that operate on Num instances (i.e. 'op2' specialized to Num)
export %inline
op2Num  : (Num a, Num b, Num c) => Show a => Show b => Show c =>
          (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullback)
       -> AD s a
       -> AD s b
       -> AD s c
op2Num = op2 0 (+) (+)

export
Show a => Backprop a => Backprop (AD s a) where
  zero = op1' $ \x =>   (zero x, zero)
  one  = op1' $ \x =>   (one  x, zero)
  add  = op2' $ \x,y => (add x y, (id,id))

export
Show a => Num a => Num (AD s a) where
  (+) = op2Num $ \x,y => (x + y, id, id)
  (*) = op2Num $ \x,y => (x*y, (y *), (x *))
  fromInteger x = MkAD0 $ lift $ var (fromInteger x) 0 -- auto' (fromInteger x)

export
Show a => Neg a => Neg (AD s a) where
  (-) = op2Num $ \x,y => (x - y, id, negate)
  negate = op1Num $ \x => (negate x, negate) -- 0 - x -- TODO check this

-- signum : Neg a => AD s a a -> AD s a a
-- signum = op1Num $ \x => (signum x, const 0)
-- 
-- Abs a => Abs (AD s a a) where
--   abs = op1Num $ \x => (abs x, (* signum x))

export
FromDouble a => FromDouble (AD s a) where
  -- fromDouble x = auto' (fromDouble x)
  fromDouble x = MkAD0 $ lift $ var (fromDouble x) 0.0 -- auto' (fromInteger x)

export
Show a => Neg a => Fractional a => Fractional (AD s a) where
  (/) = op2Num $ \x,y => (x / y, (/ y), (\g => -g*x/(y*y) ))
  recip = op1Num $ \x => (recip x, (/(x*x)) . negate)

export
Show a => Neg a => Floating a => Floating (AD s a) where
  pi = auto'' pi
  euler = auto'' euler
  exp = op1Num $ \x => (exp x, (exp x *))
  log = op1Num $ \x => (log x, (/x))
  pow = op2Num $ \x,y => (x `pow` y, (* (y * (x `pow` (y - 1)))),(* ((x `pow` y) * log x))) -- seems wrong
  sqrt = op1Num $ \x => (sqrt x, (/ (2 * sqrt x)))
  -- logBase = op2Num $ \x,y =>
  --                      let
  --                        dx = - logBase x y / (log x * x)
  --                      in ( logBase x y
  --                         , ( * dx)
  --                         , (/(y * log x))
  --                         )
  sin = op1Num $ \x => (sin x, (* cos x))
  cos = op1Num $ \x => (cos x, (* (-sin x)))
  tan = op1Num $ \x => (tan x, (/ cos x `pow` 2))
  asin = op1Num $ \x => (asin x, (/ sqrt(1 - x*x)))
  acos = op1Num $ \x => (acos x, (/ sqrt (1 - x*x)) . negate)
  atan = op1Num $ \x => (atan x, (/ (x*x + 1)))
  sinh = op1Num $ \x => (sinh x, (* cosh x))
  cosh = op1Num $ \x => (cosh x, (* sinh x))
  tanh = op1Num $ \x => (tanh x, (/ cosh x `pow` 2))
  -- asinh = op1Num $ \x => (asinh x, (/ sqrt (x*x + 1)))
  -- acosh = op1Num $ \x => (acosh x, (/ sqrt (x*x - 1)))
  -- atanh = op1Num $ \x => (atanh x, (/ (1 - x*x)))

-- -- instance Eq a => Eq (AD s a da) where -- ??? likely impossible
-- -- instance Ord (AD s a da) where -- ??? see above

-- export
-- Backprop Double Double where
--   zero = zeroNum
--   one = oneNum
--   add = addNum

export
Backprop a => Backprop b => Backprop (a,b) where
  zero (x,y) = (zero x, zero y)
  one (x,y)  = (one x , one y)
  add (x1,y1) (x2,y2) = (x1 `add` x2, y1 `add` y2)

{-
(^^.)
    :: forall b a s. (Backprop b, Backprop a, Reifies s W)
    => BVar s b
    -> Lens' b a
    -> BVar s a
x ^^. l = viewVar l x
infixl 8 ^^.
-}
{-
isoVar2
    :: (Backprop a, Backprop b, Reifies s W)
    => (a -> b -> c)
    -> (c -> (a, b))
    -> BVar s a
    -> BVar s b
    -> BVar s c
isoVar2 = E.isoVar2 E.addFunc E.addFunc
-}
||| We don't have viewpatterns in idris yet so out2 and in2 do the job of
||| managing tupled AD arguments.

-- | Evaluate (forward mode) and differentiate (reverse mode) a unary function, without committing to a specific numeric typeclass
export %inline
rad1g  : Show a -- ^ zero
      => (a -> a) -- ^ zero
      -> (b -> b) -- ^ one
      -> (forall s . AD s a -> AD s b)
      -> a -- ^ function argument
      -> (b, a) -- ^ (result, adjoint)
rad1g zeroa oneb f x = runST $ do
  xr <- var x (zeroa x)
  -- pure $ unsafePerformIO $ putStrLn $ "rad1 zero: " ++ show !(readSTRef xr)
  zr' <- evalContT $
    resetT $ do
      let
        z = f (MkAD0 (pure xr))
      zr <- unAD0 z
      lift $ modifySTRef zr (mapDual oneb)
      pure zr
  (MkD z _) <- readSTRef zr'
  (MkD _ x_bar) <- readSTRef xr
  pure (z, x_bar)



-- | Evaluate (forward mode) and differentiate (reverse mode) a binary function, without committing to a specific numeric typeclass
export %inline
rad2g  : (a -> a) -- ^ zero
      -> (b -> b) -- ^ zero
      -> (c -> c) -- ^ one
      -> (forall s . AD s a -> AD s b -> AD s c)
      -> a -> b
      -> (c, (a, b)) -- ^ (result, adjoints)
rad2g zeroa zerob onec f x y = runST $ do
  xr <- var x (zeroa x)
  yr <- var y (zerob y)
  zr' <- evalContT $
    resetT $ do
      let
        z = f (MkAD0 (pure xr)) (MkAD0 (pure yr))
      zr <- unAD0 z
      lift $ modifySTRef zr (mapDual onec)
      pure zr
  (MkD z _) <- readSTRef zr'
  (MkD _ x_bar) <- readSTRef xr
  (MkD _ y_bar) <- readSTRef yr
  pure (z, (x_bar, y_bar))

-- | Evaluate (forward mode) and differentiate (reverse mode) a function of a 'Traversable'
--
-- In linear algebra terms, this computes the gradient of a scalar function of vector argument
export %inline
radNg  : Traversable t =>
         a -- ^ zero
      -> b -- ^ one
      -> (forall s . t (AD s a) -> AD s b)
      -> t a -- ^ argument vector
      -> (b, t (Lazy a)) -- ^ (result, gradient vector)
radNg zeroa onea f xs = runST $ do
  xrs <- traverse (`var` zeroa) xs
  zr' <- evalContT $
    resetT $ do
      let
        (MkAD0 z) = f (map pure xrs)
      zr <- z
      lift $ modifySTRef zr (mapDual (const onea))
      pure zr
  (MkD z _) <- readSTRef zr'
  xs_bar <- traverse readSTRef xrs
  let xs_bar_d = dual <$> xs_bar
  pure (z, xs_bar_d)


-- | Evaluate (forward mode) and differentiate (reverse mode) a unary function
--
-- >>> rad1 (\x -> x * x) 1
-- (1, 2)
export %inline
rad1  : (Backprop a, Backprop b, Show a) =>
        (forall s . AD s a -> AD s b) -- ^ function to be differentiated
     -> a -- ^ function argument
     -> (b, a) -- ^ (result, adjoint)
rad1 = rad1g zero one

-- | Evaluate (forward mode) and differentiate (reverse mode) a binary function
--
-- >>> rad2 (\x y -> x + y + y) 1 1
-- (1,2)
--
-- >>> rad2 (\x y -> (x + y) * x) 3 2
-- (15,(8,3))
export %inline
rad2  : (Backprop a, Backprop b, Backprop c) =>
        (forall s . AD s a -> AD s b -> AD s c) -- ^ function to be differentiated
     -> a
     -> b
     -> (c, (a, b)) -- ^ (result, adjoints)
rad2 = rad2g zero zero one

export %inline
grad  : (Traversable t, Num a, Num b) =>
        (forall s . t (AD s a) -> AD s b)
     -> t a -- ^ argument vector
     -> (b, t (Lazy a)) -- ^ (result, gradient vector)
grad = radNg 0 1

export %inline
gradBP : (Backprop a, Backprop b, Show a) => (forall s . AD s a -> AD s b) -> a -> a
gradBP f = snd . rad1 f

export %inline
gradBP2 : (Backprop a, Backprop b, Backprop c) => (forall s . AD s a -> AD s b -> AD s c) -> a -> b -> (a,b)
gradBP2 f x y = snd $ rad2 f x y

-- i feel eval is modifying the state when it shoulnd't
export %inline
evalBP : (Backprop a, Backprop b, Show a) => (forall s . AD s a -> AD s b) -> a -> b
evalBP f x = fst $ rad1 f x

export %inline
evalBP2 : (Backprop a, Backprop b, Backprop c) => (forall s . AD s a -> AD s b -> AD s c) -> a -> b -> c
evalBP2 f x y = fst $ rad2 f x y


opl  : Backprop a => Backprop b
     => ContT x (ST s) (DVar s (a,b))
     -> ContT x (ST s) (DVar s a)
opl ioa = do
  rab <- ioa
  resetT $ lift $ modifySTRef rab (mapDual one)
  (MkD (z,_) (x_bar,_)) <- lift $ readSTRef rab
  lift $ var z x_bar

opr  : Backprop a => Backprop b
     => ContT x (ST s) (DVar s (a,b))
     -> ContT x (ST s) (DVar s b)
opr ioa = do
  rab <- ioa
  resetT $ lift $ modifySTRef rab (mapDual one)
  (MkD (_,z) (_,x_bar)) <- lift $ readSTRef rab
  lift $ var z x_bar

export %inline
out2 : Show a => Show b => Backprop a => Backprop b => AD z (a, b) -> (AD z a, AD z b)
-- out2 p = ( MkAD0 (opl (unAD0 p))
         -- , MkAD0 (opr (unAD0 p))
         -- )
out2 p = ( op1 zero addLeft  (\(x, y) => (x, ( ,y))) p
         , op1 zero addRight (\(x, y) => (y, (x, ))) p
         )
  where
    addLeft : (a,b) -> (a,b) -> (a,b)
    addLeft (x1,y) (x2,_)  = (x1 `add` x2, y)
    addRight : (a,b) -> (a,b) -> (a,b)
    addRight (x,y1) (_,y2) = (x, y1 `add` y2)

export %inline
in2 : Show a => Show b => Backprop a => Backprop b => AD z a -> AD z b -> AD z (a, b)
in2 = op2' (\x,y => ((x, y), (fst, snd)))
