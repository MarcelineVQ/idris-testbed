module BP2

import Control.Monad.State

import public BP.Backprop

import Data.ArrayFire

import public BP.Generic

-- import Data.Strong.Matrix
-- import Data.Strong.Arr
-- import Data.Strong.Arr.Interfaces
import Numeric.Floating

import Control.Monad.Trans
import public Control.Monad.ST
import public Control.Monad.Cont

import public Data.Stream

-- import Net.Activation

import Util

-- import BP.Generic

import Generics.Derive
import Generics.Newtype
%language ElabReflection


public export
Mat : (i : Nat) -> (o : Nat) -> Type
Mat i o = AFArray [i,o] F64

public export
Arr : (i : Nat) -> Type
Arr i = AFArray [i] F64

public export
data Raf = MkRaf Double
%runElab derive "Raf"
  [Generic, Eq, Ord, Num, Neg, Abs, Fractional, FromDouble]

public export
data Raff a b = MkRaff a b
%runElab derive "Raff"
  [Generic, Eq, Ord, Num, Neg, Abs, Fractional, FromDouble, Integral]


export
{i:_} -> Backprop (Arr i) where
  zero _ = 0
  one _ = 1
  add = (+)

export
{i:_} -> {o:_} -> Backprop (Mat i o) where
  zero _ = 0
  one _ = 1
  add = (+)

infixr 7 :&
infixr 7 :&&

public export
data Tup2 : Type -> Type -> Type where
  MkT2 : a -> b -> Tup2 a b

%runElab derive "Tup2"
  [Generic,Meta,Eq,Ord,DecEq,Show,Num,Neg,Abs,Fractional,FromDouble,Backprop]

public export
data Tup3 : Type -> Type -> Type -> Type where
  MkT3 : a -> b -> c -> Tup3 a b c

%runElab derive "Tup3"
  [Generic,Meta,Eq,Ord,DecEq,Show,Num,Neg,Abs,Fractional,FromDouble,Backprop]

public export
data Tup4 : Type -> Type -> Type -> Type -> Type where
  MkT4 : a -> b -> c -> d -> Tup4 a b c d

%runElab derive "Tup4"
  [Generic,Meta,Eq,Ord,DecEq,Show,Num,Neg,Abs,Fractional,FromDouble,Backprop]

public export
data Tup5 : Type -> Type -> Type -> Type -> Type -> Type where
  MkT5 : a -> b -> c -> d -> e -> Tup5 a b c d e

%runElab derive "Tup5"
  [Generic,Meta,Eq,Ord,DecEq,Show,Num,Neg,Abs,Fractional,FromDouble,Backprop]

public export
data (:&) : Type -> Type -> Type where
  (:&&) : a -> b -> a :& b

%runElab derive ":&"
  [Generic,Meta,Eq,Ord,DecEq,Show,Num,Neg,Abs,Fractional,FromDouble,Backprop]

export
Functor (a :&) where
  map f (x :&& y) = x :&& f y

export
Bifunctor (:&) where
  bimap f g (x :&& y) = f x :&& g y

-- export
-- Backprop a => Backprop b => Backprop (a :& b) where
--   zero (x :&& y)= zero x :&& zero y
--   one (x :&& y) = one x :&& one y
--   add (x1 :&& y1) (x2 :&& y2) = add x1 x2 :&& add y1 y2

export
fst : a :& b -> a
fst (x :&& _) = x

export
snd : a :& b -> b
snd (_ :&& y) = y

-- Other variations of this I've tried didn't modify rda0 properly, breaking the
-- relation neccesary for backpropogation. This seems to be correct currently.

||| We don't have viewpatterns in idris yet so out2 and in2 do the job of
||| managing tupled AD arguments.
export
out2 : Backprop a => Backprop b => AD z (a :& b) -> (AD z a) :& (AD z b)
out2 p = op1 zero (\rda0,gyd => mapFst (`add` fst gyd) rda0)
                  (\(x :&& y) => (x, (:&& y))) p
     :&& op1 zero (\rda0,gyd => mapSnd (`add` snd gyd) rda0)
                  (\(x :&& y) => (y, (x :&&))) p

-- for testing against out2, using out2 twice instead of out3 once works exactly the same
export
out3 : Backprop a => Backprop b => Backprop c => AD z (Tup3 a b c) -> Tup3 (AD z a) (AD z b) (AD z c)
out3 p = MkT3
     (op1 zero (\(MkT3 da db dc),(MkT3 gda gdb gdc) => MkT3 (gda `add` da) db dc)
                  (\(MkT3 x y z) => (x, (\x => MkT3 x y z))) p)
     (op1 zero (\(MkT3 da db dc),(MkT3 gda gdb gdc) => MkT3 da (gdb `add` db) dc)
                  (\(MkT3 x y z) => (y, (\y => MkT3 x y z))) p)
     (op1 zero (\(MkT3 da db dc),(MkT3 gda gdb gdc) => MkT3 da db (gdc `add` dc))
                  (\(MkT3 x y z) => (z, (\z => MkT3 x y z))) p)

export
in2 : Backprop a => Backprop b => AD z a -> AD z b -> AD z (a :& b)
in2 = op2' (\x,y => (x :&& y, (fst, snd)))

export
linReg : Num a => Backprop a => AD z (a :& a) -> AD z a -> AD z a
linReg ab x with (out2 ab)
  _ | a' :&& b' = b' * x + a'

export
linRegOut22 : Neg a => Num a => Backprop a => AD z (a :& a :& a) -> AD z a -> AD z a
linRegOut22 ab x = case mapSnd out2 (out2 ab) of
                    (a' :&& b' :&& z') => b' * x + a'

-- these - z' ones need 0.01 traning rate
export
linRegOut22' : Neg a => Num a => Backprop a => AD z (a :& a :& a) -> AD z a -> AD z a
linRegOut22' ab x = case mapSnd out2 (out2 ab) of
                    (a' :&& b' :&& z') => b' * x + a' - z'

-- Created to test against nested out2. Nested out2 turns out exacly the same.
-- Thus later numerical errors aren't due to out2
export
linRegT3 : Neg a => Num a => Backprop a => AD z (Tup3 a a a) -> AD z a -> AD z a
linRegT3 abc x = case out3 abc of
                     (MkT3 a' b' z') => b' * x + a'

-- these - z' ones need 0.01 traning rate
export
linRegT3' : Neg a => Num a => Backprop a => AD z (Tup3 a a a) -> AD z a -> AD z a
linRegT3' abc x = case out3 abc of
                     (MkT3 a' b' z') => b' * x + a' - z'

export
linRegSamps : List (Double, Double)
linRegSamps = [(1,1),(2,3),(3,5),(4,7),(5,9)]

export
squaredErrorGrad : (Backprop p, Backprop b, Num a, Num b, Neg b)
    => (forall z. AD z p -> AD z a -> AD z b)      -- ^ Model
    -> a                -- ^ Observed input
    -> b                -- ^ Observed output
    -> p                -- ^ Parameter guess
    -> p                -- ^ Gradient
squaredErrorGrad f x targ = gradBP $ \p => (f p (auto'' x) - auto'' targ) ^ 2

export
squaredErrorGrad' : (Backprop p, Backprop b, Num a, Num b, Neg b)
    => (forall z. AD z p -> AD z a -> AD z b)      -- ^ Model
    -> a                -- ^ Observed input
    -> b                -- ^ Observed output
    -> p                -- ^ Parameter guess
    -> (b,p)                -- ^ Gradient
squaredErrorGrad' f x targ = rad1 $ \p => (f p (auto'' x) - auto'' targ) ^ 2

export
trainModel
     : Backprop p
    => Num b
    => Num a
    => Neg b
    => FromDouble p
    => Neg p
    => Backprop b
    => p -- learningrate
    -> (forall z. AD z p -> AD z a -> AD z b)      -- ^ model to train
    -> p                -- ^ initial parameter guess
    -> List (a,b)          -- ^ list of observations
    -> p                -- ^ updated parameter guess
trainModel r f = foldl $ \p,(x,y) => p - r * squaredErrorGrad f x y p

export
scanl : (res -> a -> res) -> res -> List a -> List res
scanl f q []      = [q]
scanl f q (x::xs) = q :: scanl f (f q x) xs

export
trainModel'
     : Backprop p
    => Num b
    => Num a
    => Neg b
    => FromDouble p
    => Neg p
    => Backprop b
    => p -- learningrate
    -> (forall z. AD z p -> AD z a -> AD z b)      -- ^ model to train
    -> p                -- ^ initial parameter guess
    -> List (a,b)          -- ^ list of observations
    -> List p                -- ^ updated parameter guess
trainModel' r f = BP2.scanl $ \p,(x,y) => p - r * squaredErrorGrad f x y p

export
linRegTest : Double :& Double
linRegTest =
  trainModel 0.1 linReg (10.0 :&& -9.0) (take 5000 $ cycle [(1,1),(2,3),(3,5),(4,7),(5,9)])

export
app  : Backprop (Mat m n)
    => Backprop (Arr n)
    => Backprop (Arr m)
    => AD z (Mat m n)
    -> AD z (Arr n)
    -> AD z (Arr m)
app = op2' $ \xs,y =>
    ( xs #> y
    , (\dc => dc `mulOuter` y) -- |A = |CB^T
    , (\dc => transpose xs #> dc)) -- |B = A^T|C

export
dot  : {s:_}
    -> Backprop (Arr s)
    => AD z (Arr s)
    -> AD z (Arr s)
    -> AD z Double
dot = op2' $ \x,y =>
    ( x `dotAll` y
    , (\dc => constant' dc * y)  -- |A = |CB^T
    , (\dc => x * constant' dc)) -- |B = A^T|C

export
(#>) : Backprop (Mat h w)
    => Backprop (Arr w)
    => Backprop (Arr h)
    => AD z (Mat h w) -> AD z (Arr w) -> AD z (Arr h)
x #> y = app x y

Model' : {z : Type} -> (p : Type) -> (s : Type) -> (a : Type) -> (b : Type) -> Type
Model' p s a b = AD z p -> AD z s -> AD z a -> AD z b

Optional : Maybe Type -> Type
Optional (Just x) = x
Optional Nothing = Void

data RealizedModel : Type where
  MkRM : paramsTy -> Model' paramsTy (Optional stateTy) a b -> RealizedModel

--------------------------------------------------
-- FFNN
--------------------------------------------------

-- this doens't seem to work any better than logistic
-- logisticOp : Backprop a => Neg a => Floating a => AD s a -> AD s a
-- logisticOp = op1' $ \x =>
--     let lx = logistic x
--     in  (lx, \g => lx * (1 - lx) * g)

public export
Model : {z : Type} -> (p : Type) -> (a : Type) -> (b : Type) -> Type
Model p a b =  AD z p -> AD z a -> AD z b

logistic : Neg a => Floating a => a -> a
logistic x = 1 / (1 + exp (-x))

export
feedForwardLog : {o,i:_} -> Model (Mat o i :& Arr o) (Arr i) (Arr o)
feedForwardLog wb x with (out2 wb)
  _ | (w :&& b) = logistic (w #> x + b)

export
logReg : Model (Double :& Double) Double Double
logReg ab = logistic . linReg ab

export
andSamps : List (Arr 2, Arr 1)
andSamps = [(vec2 0.0 0.0, 0), (vec2 1.0 0.0, 0), (vec2 0.0 1.0, 0), (vec2 1.0 1.0, 1)]

export
feedForward : {o,i:_} -> Model (Mat o i :& Arr o) (Arr i) (Arr o)
feedForward wb x with (out2 wb)
  _ | (w :&& b) = w #> x + b

export
feedForwardLog' : {o,i:_} -> Model (Mat o i :& Arr o) (Arr i) (Arr o)
feedForwardLog' wb = logistic . feedForward wb

export
konst : {n:_} -> AD z Double -> AD z (Arr n)
konst = op1' (\x => (constant _ _ x, sumAll)) -- sumArray seems, wrong? shouldn't it be like  sumArray / s

export
sumElements : {n:_} -> Num a => Backprop a => AD z (Arr n) -> AD z Double
sumElements = op1' (\a => (sumAll a, constant _ _)) -- shouldn't it be newArray' (xs/s)

-- untested, doesn't seem to work
export
softMax : {n:_} -> AD z (Arr n) -> AD z (Arr n)
softMax x = let expx = exp x
            in konst (1 / sumElements expx) * expx

-- untested
export
feedForwardSoftMax : {o,i:_} -> Model (Mat o i :& Arr o) (Arr i) (Arr o)
feedForwardSoftMax wb = softMax . feedForward wb

export
xorSamps : List (Arr 2, Arr 1)
xorSamps = [(vec2 0.0 0.0, 0), (vec2 1.0 0.0, 1), (vec2 0.0 1.0, 1), (vec2 1.0 1.0, 0)]



-- feedForwardLog' seems to work fine up to this point

infixr 8 <~
export
-- have to specify that the z are the same
(<~) : (Backprop p, Backprop q)
    => Model {z}  p       b c
    -> Model {z}       q  a b
    -> Model {z} (p :& q) a c
(f <~ g) pq with (out2 pq)
  _ | (p' :&& q') = f p' . g q'

-- twoLayer computes andSamps fairly, but not xorSamps
-- :exec printLn $ evalBP2 twoLayer (trainModel 0.1 twoLayer 0.5 (take 10000 $ cycle xorSamps)) (fromList [1,1])
-- three layers doesn't fair any better. How can feedForwardLog work but not
-- twoLayer? They use the same derivation math and I've shown :& to be safe
-- elsewhere. three layers is worse on andSamps. Way worse, pathetically worse.
-- Bafflingly worse. More layer moves xorSamps closer and closer to 0.5
export
twoLayer : Model ? (Arr 2) (Arr 1)
twoLayer = feedForwardLog' {i=4} <~ feedForwardLog'

export
threeLayer : Model ? (Arr 2) (Arr 1)
threeLayer = feedForwardLog' {i=4} <~ feedForwardLog' {i=4} <~ feedForwardLog'

-- progressively less accurate, or rather progressively closer to 0.5
export
fourLayer : Model ? (Arr 2) (Arr 1)
fourLayer = feedForwardLog' {i=4} <~ feedForwardLog' {i=4} <~ feedForwardLog' {i=4} <~ feedForwardLog'

export
testo : Arr 1
testo = evalBP2 twoLayer (trainModel 0.1 twoLayer 0.5 (take 2000 $ cycle ([(vec2 0.0 0.0, 0), (vec2 1.0 0.0, 1), (vec2 0.0 1.0, 1), (vec2 1.0 1.0, 0)]))) (vec2 1.0 1.0)

export
testo2 : Arr 1
testo2 = evalBP2 feedForwardLog' (trainModel 0.1 feedForwardLog' 0.5 (take 2000 $ cycle ([(vec2 0.0 0.0, 0), (vec2 1.0 0.0, 1), (vec2 0.0 1.0, 1), (vec2 1.0 1.0, 0)]))) (vec2 1.0 1.0)

--------------------------------------------------
-- RNN
--------------------------------------------------



public export
-- %tcinline
ModelS : {z : Type} -> (p : Type) -> (s: Type) -> (a : Type) -> (b : Type) -> Type
ModelS p s a b = AD z p -> AD z a -> AD z s -> (AD z b, AD z s)

export
ar2 : AD z (Double :& Double :& Double) -> AD z Double -> AD z Double -> (AD z Double, AD z Double)
ar2 p yLast yLastLast
  = case mapSnd out2 (out2 p) of
      (c :&& y1 :&& y2) => (c + y1 * yLast + y2 * yLastLast, yLast)

export
ar2' : ModelS (Double :& Double :& Double) Double Double Double
ar2' p yLast yLastLast
  = case mapSnd out2 (out2 p) of
      (c :&& y1 :&& y2) => (c + y1 * yLast + y2 * yLastLast, yLast)



{-

fcrnn : ModelS (Mat o i, Mat o o, Arr o) (Arr o) (Arr i) (Arr o) 
fcrnn (BV (wX,wS,b)) (BV x) (BV s) = let y = wX #> x + wS #> s + b
                        in  (BV y, BV $ logistic <$> y)

fcrnn' : {o:_} -> ModelS (Mat o i, Mat o o, Arr o) (Arr o) (Arr i) (Arr o) 
fcrnn' p x s with (out3 p)
  _ | (wX,wS,b) = let y = wX #> x + wS #> s + b
                  in  (y, ?dsfd)


fcarnn : ModelS ((Mat o i, Mat o o, Arr o, Arr o)) (Arr o) (Arr i) (Arr o) 
fcarnn (BV (wX,wS,wSm,b)) (BV x) (BV s) = let y = (wX #> x + wS #> s + b) * wSm
                                          in  (BV y, BV $ logistic <$> y)

fcarnn' : {o:_} -> ModelS (Mat o i, Mat o o, Arr o, Arr o) (Arr o) (Arr i) (Arr o)
fcarnn' p x s with (out4 p)
  _ | (wX,wS,wSm,b) = let y = (wX #> x + wS #> s + b) * wSm
                      in  (y, logistic <$> y)

infixr 8 <*~*
(<*~*)
  : (Backprop p, Backprop q, Backprop s, Backprop t)
    => ModelS {z}  p     s    b c
    -> ModelS {z}    q     t  a b
    -> ModelS {z} (p,q) (s,t) a c
(f <*~* g) (BV (p, q)) x (BV (s, t)) =
  let (y, BV t') = g (BV q) x (BV t)
      (z, BV s') = f (BV p) y (BV s)
  in (z, BV (s', t'))

infixr 8 <*~
(<*~)
   : (Backprop p, Backprop q)
    => Model  {z}  p         b c
    -> ModelS {z}       q  s a b
    -> ModelS {z} (p,   q) s a c
(f <*~ g) (BV (p, q)) x = mapFst (f (BV p)) . g (BV q) x

mapS : (forall z. Ref z W => AD' z b -> AD' z c)
    -> ModelS {z} p s a b
    -> ModelS {z} p s a c
-- mapS g f s a b = let (z,s') = f s a b in (g z,s')
mapS f g p x = mapFst f . g p x

toS : Model {z} p a b -> ModelS {z} p s a b
toS f p x s = (f p x, s)

-- twoLayerRNN : ModelS _ (Arr 5,Arr 5) (Arr 20) (Arr 5)
-- _ isn't good enough, we need to search via ?
-- i, used here, is the hidden layers of the model
twoLayerRNN : ModelS ? ? (Arr 20) (Arr 5)
twoLayerRNN = fcrnn {i=10} <*~* mapS (map logistic) fcrnn

-- i, used here, is the hidden layers of the model
threeLayerRNN : ModelS ? ? (Arr 20) (Arr 5)
threeLayerRNN = fcrnn {i=10} <*~* mapS (map logistic) (fcrnn {i=20}) <*~* mapS (map logistic) fcrnn

hybrid : ModelS ? ? (Arr 40) (Arr 10)
hybrid = feedForwardLog {i=20}
         <*~  mapS (map logistic) (fcrnn {i=20})
         <*~* mapS (map logistic) fcrnn

unroll : ModelS p s a b -> ModelS p s (List a) (List b)
unroll = ?dssffd

-}

main : IO ()
main = printLn BP2.testo
