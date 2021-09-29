module BP.Backprop

import Numeric.Floating

import Control.Monad.Trans
import public Control.Monad.ST
import public Control.Monad.Cont

import Data.Strong.Array

import Data.List

public export
record D a where
  constructor MkD
  primal : a
  dual : a

export
mapPrimal : (a -> a) -> D a -> D a
mapPrimal f (MkD x y) = MkD (f x) y

export
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
export
zeroNum : Num a => a -> a
zeroNum _ = 0

-- | 'add' for instances of 'Num'.
export
addNum : Num a => a -> a -> a
addNum = (+)

-- | 'one' for instances of 'Num'. lazy in its argument.
export
oneNum : Num a => a -> a
oneNum _ = 1


public export
interface Backprop a where
  constructor MkBackprop
  zero : a -> a
  one : a -> a
  add : a -> a -> a

-- believe_me: even more deadly than undefined
export
auto' : Backprop a => a -> AD s a
auto' x = MkAD0 $ lift $ var x (zero x)
-- auto' x = MkAD0 $ lift $ var x (believe_me 0)

export
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
export
op1_  : (b -> b) -- ^ zero
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
    pure ry

-- | Lift a unary function
-- The first two arguments constrain the types of the adjoint values of the
-- output and input variable respectively, see 'op1Num' for an example.
-- The third argument is the most interesting: it specifies at once how to
-- compute the function value and how to compute the sensitivity with respect to
-- the function parameter.
-- Note: the type parameters are completely unconstrained.
export
op1  : (b -> b) -- ^ zero
    -> (a -> a -> a) -- ^ plus
    -> (a -> (b, b -> a)) -- ^ returns : (function result, pullback)
    -> AD s a
    -> AD s b
op1 z plusa f (MkAD0 ioa) = MkAD0 $ op1_ z plusa f ioa

export
op1'  : Backprop a => Backprop b
    => (a -> (b, b -> a))
    -> AD s a
    -> AD s b
op1' f (MkAD0 ioa) = MkAD0 $ op1_ zero add f ioa


-- | Helper for constructing unary functions that operate on Num instances (i.e. 'op1' specialized to Num)
export
op1Num  : (Num a, Num b) =>
          (a -> (b, b -> a)) -- ^ returns : (function result, pullback)
       -> AD s a
       -> AD s b
op1Num = op1 zeroNum addNum

-- | Lift a binary function
export
op2_  : c -- ^ zero
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
    pure ry

-- | Lift a binary function
--
-- See 'op1' for more information.
export
op2  : c -- ^ zero
    -> (a -> a -> a) -- ^ plus
    -> (b -> b -> b) -- ^ plus
    -> (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullbacks)
    -> (AD s a -> AD s b -> AD s c)
op2 z plusa plusb f (MkAD0 ioa) (MkAD0 iob) = MkAD0 $ op2_ z plusa plusb f ioa iob

export
op2'_  : (c -> c) -- ^ zero
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
    pure ry

export
op2'  : Backprop a => Backprop b => Backprop c
    => (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullbacks)
    -> (AD s a -> AD s b -> AD s c)
op2' f (MkAD0 ioa) (MkAD0 iob) = MkAD0 $ op2'_ zero add add f ioa iob

-- | Helper for constructing binary functions that operate on Num instances (i.e. 'op2' specialized to Num)
export
op2Num  : (Num a, Num b, Num c) =>
          (a -> b -> (c, c -> a, c -> b)) -- ^ returns : (function result, pullback)
       -> AD s a
       -> AD s b
       -> AD s c
op2Num = op2 0 (+) (+)

export
Backprop a => Backprop (AD s a) where
  zero = op1' $ \x =>   (zero x, zero)
  one  = op1' $ \x =>   (one  x, zero)
  add  = op2' $ \x,y => (add x y, (id,id))

export
Num a => Num (AD s a) where
  (+) = op2Num $ \x,y => (x + y, id, id)
  (*) = op2Num $ \x,y => (x*y, (y *), (x *))
  fromInteger x = MkAD0 $ lift $ var (fromInteger x) 0 -- auto' (fromInteger x)

export
Neg a => Neg (AD s a) where
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
Neg a => Fractional a => Fractional (AD s a) where
  (/) = op2Num $ \x,y => (x / y, (/ y), (\g => -g*x/(y*y) ))
  recip = op1Num $ \x => (recip x, (/(x*x)) . negate)

export
Neg a => Floating a => Floating (AD s a) where
  pi = auto'' pi
  euler = auto'' euler
  exp = op1Num $ \x => (exp x, (exp x *))
  log = op1Num $ \x => (log x, (/x))
  pow = ?sdfsfd
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


-- | Evaluate (forward mode) and differentiate (reverse mode) a unary function, without committing to a specific numeric typeclass
export
rad1g  : (a -> a) -- ^ zero
      -> (b -> b) -- ^ one
      -> (forall s . AD s a -> AD s b)
      -> a -- ^ function argument
      -> (b, a) -- ^ (result, adjoint)
rad1g zeroa oneb f x = runST $ do
  xr <- var x (zeroa x)
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
export
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
export
radNg  : Traversable t =>
         a -- ^ zero
      -> b -- ^ one
      -> (forall s . t (AD s a) -> AD s b)
      -> t a -- ^ argument vector
      -> (b, t a) -- ^ (result, gradient vector)
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
export
rad1  : (Backprop a, Backprop b) =>
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
export
rad2  : (Backprop a, Backprop b, Backprop c) =>
        (forall s . AD s a -> AD s b -> AD s c) -- ^ function to be differentiated
     -> a
     -> b
     -> (c, (a, b)) -- ^ (result, adjoints)
rad2 = rad2g zero zero one

-- | Evaluate (forward mode) and differentiate (reverse mode) a function of a 'Traversable'
--
-- In linear algebra terms, this computes the gradient of a scalar function of vector argument
--
--
-- @
-- sqNorm :: Num a => [a] -> a
-- sqNorm xs = sum $ zipWith (*) xs xs
--
-- p :: [Double]
-- p = [4.1, 2]
-- @
--
-- >>> grad sqNorm p
-- (20.81,[8.2,4.0])
export
grad  : (Traversable t, Num a, Num b) =>
        (forall s . t (AD s a) -> AD s b)
     -> t a -- ^ argument vector
     -> (b, t a) -- ^ (result, gradient vector)
grad = radNg 0 1

-- export
-- sqNorm : Num a => List a -> a
-- sqNorm xs = sum $ zipWith (*) xs xs
-- 
-- export
-- p : List Double
-- p = [4.1, 2.0]

-- >>> grad sqNorm p
-- (20.81,[8.2,4.0])

export
gradBP : (Backprop a, Backprop b) => (forall s . AD s a -> AD s b) -> a -> a
gradBP f = snd . rad1 f

export
gradBP2 : (Backprop a, Backprop b, Backprop c) => (forall s . AD s a -> AD s b -> AD s c) -> a -> b -> (a,b)
gradBP2 f x y = snd $ rad2 f x y

-- i feel eval is modifying the state when it shoulnd't
export
evalBP : (Backprop a, Backprop b) => (forall s . AD s a -> AD s b) -> a -> b
evalBP f x = fst $ rad1 f x

export
evalBP2 : (Backprop a, Backprop b, Backprop c) => (forall s . AD s a -> AD s b -> AD s c) -> a -> b -> c
evalBP2 f x y = fst $ rad2 f x y
