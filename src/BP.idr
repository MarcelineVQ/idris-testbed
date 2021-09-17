module BP

import Control.Monad.State

import public BP.Backprop

import Data.Strong.Matrix
import Data.Strong.Array
import Data.Strong.Array.Interfaces
import Numeric.Floating

import public Data.Stream

import Net.Activation

import Util

-- import BP.Backprop

import Generics.Derive
%language ElabReflection

L : (o : Nat) -> (i : Nat) -> Type
L o i = Matrix o i Double

R : (o : Nat) -> Type
R o = Array o Double

-- Still not sure how to translate properly:
-- type Model p a b = forall z. AD z p -> AD z a -> AD z b
public export
Model : {z : Type} -> Type -> Type -> Type -> Type
Model p a b = AD z p -> AD z a -> AD z b


infixr 7 :&
infixr 7 :&&
public export
data (:&) : Type -> Type -> Type where
  (:&&) : a -> b -> a :& b

export
Show a => Show b => Show (a :& b) where
  show (a :&& b) = "(" ++ show a ++ " :&& " ++ show b ++ ")"

export
FromDouble a => FromDouble b => FromDouble (a :& b) where
  fromDouble x = fromDouble x :&& fromDouble x

export
Bifunctor (:&) where
  bimap f g (x :&& y) = f x :&& g y

export
Backprop a => Backprop b => Backprop (a :& b) where
  zero (x :&& y)= zero x :&& zero y
  one (x :&& y) = one x :&& one y
  add (x1 :&& y1) (x2 :&& y2) = add x1 x2 :&& add y1 y2

export
fst : a :& b -> a
fst (x :&& _) = x

export
snd : a :& b -> b
snd (_ :&& y) = y

export
Num a => Num b => Num (a :& b) where
   (x1 :&& y1) + (x2 :&& y2) = (x1 + x2) :&& (y1 + y2)
   (x1 :&& y1) * (x2 :&& y2) = (x1 * x2) :&& (y1 * y2)
   fromInteger x = (fromInteger x) :&& (fromInteger x)

export
Neg a => Neg b => Neg (a :& b) where
  (x1 :&& y1) - (x2 :&& y2) = (x1 - x2) :&& (y1 - y2)
  negate (x :&& y) = negate x :&& negate y

export
out2 : Backprop a => Backprop b => AD z (a :& b) -> (AD z a) :& (AD z b)
out2 p = let fst = op1' (\(x :&& y) => (x, (\x => x :&& y))) p
             snd = op1' (\(x :&& y) => (y, (\y => x :&& y))) p
         in fst :&& snd

export
in2 : Backprop a => Backprop b => AD z a -> AD z b -> AD z (a :& b)
in2 = op2' (\x,y => (x :&& y, (fst,snd)))

{-
pattern (:&&) :: (Backprop a, Backprop b, Reifies z W)
              => BVar z a -> BVar z b -> BVar z (a :& b)
pattern x :&& y <- (\xy -> (xy ^^. t1, xy ^^. t2)->(x, y))
  where
    (:&&) = isoVar2 (:&) (\case x :& y -> (x, y))
-}

-- linReg : Model (Double :& Double) Double Double
export
linReg : Num a => Backprop a => AD z (a :& a) -> AD z a -> AD z a
linReg ab v with (out2 ab)
  _ | x :&& y = y * v + x

export
gradBP : (Backprop a, Backprop b) => (forall s . AD s a -> AD s b) -> a -> a
gradBP f = snd . rad1 f

export
squaredErrorGrad : (Backprop p, Backprop b, Num a, Num b, Neg b)
    => (forall z. AD z p -> AD z a -> AD z b)      -- ^ Model
    -> a                -- ^ Observed input
    -> b                -- ^ Observed output
    -> p                -- ^ Parameter guess
    -> p                -- ^ Gradient
squaredErrorGrad f x targ = gradBP $ \p => (f p (auto'' x) - auto'' targ) ^ 2

export
trainModel
     : Backprop p
    => Num b
    => Num a
    => Neg b
    => FromDouble p
    => Neg p
    => Backprop b
    => (forall z. AD z p -> AD z a -> AD z b)      -- ^ model to train
    -> p                -- ^ initial parameter guess
    -> List (a,b)          -- ^ list of observations
    -> p                -- ^ updated parameter guess
trainModel f = foldl $ \p,(x,y) => p - 0.1 * squaredErrorGrad f x y p

export
samps : List (Double,Double)
samps = [(1,1),(2,3),(3,5),(4,7),(5,9)]



export
linReg' : AD z Double -> AD z Double -> AD z Double
linReg' a b = b * 5 + a

export
linRegTest : AD z Double -> AD z Double
linRegTest = linReg (in2 0.5 (-0.1))

export
linRegTest' : (Double, (Double :& Double, Double))
linRegTest' = rad2 linReg (0.5 :&& (-0.1)) 5




app  : Backprop (Matrix m n a)
    => Backprop (Array n a)
    => AD z (Matrix m n a)
    -> AD z (Array n a)
    -> AD z (Array m a)
-- app = op2 (zeroNum 0) addNum addNum $ \xs y ->
--     ( xs `H.app` y
--     , \d -> (d `H.outer` y, H.tr xs `H.app` d)
--     )

-- export
-- dot  : {s:_} -> Num a
--     => Backprop (Array s a)
--     => AD z (Array s a)
--     -> AD z (Array s a)
--     -> AD z a
-- dot = op2 zeroNum addNum addNum $ \x,y =>
--     ( x `dotArray` y
--     , (\d => newArray' d * y)
--     , (\d => newArray' d * y))

-- 
-- 
-- (#>) : AD' z (L h w) -> AD' z (R w) -> AD' z (R h)
-- x #> y = app x y

public export
ModelS : Type -> Type -> Type -> Type -> Type
ModelS p s a b = {z : _} -> AD z p -> AD z a -> AD z s -> (AD z b, AD z s)

-- ar2 : ModelS (Double, Double, Double) Double Double Double
-- ar2 (BV (c,y1,y2)) (BV yLast) (BV yLastLast)
--   = (BV $ c + y1 * yLast + y2 * yLastLast, BV yLast)
-- 

-- ar2' : ModelS (Double, Double, Double) Double Double Double
-- ar2' p yLast yLastLast with (out3 p)
  -- _ | (c,y1,y2) = (c + y1 * yLast + y2 * yLastLast, yLast)



{-

fcrnn : ModelS (L o i, L o o, R o) (R o) (R i) (R o) 
fcrnn (BV (wX,wS,b)) (BV x) (BV s) = let y = wX #> x + wS #> s + b
                        in  (BV y, BV $ logistic <$> y)

fcrnn' : {o:_} -> ModelS (L o i, L o o, R o) (R o) (R i) (R o) 
fcrnn' p x s with (out3 p)
  _ | (wX,wS,b) = let y = wX #> x + wS #> s + b
                  in  (y, ?dsfd)


fcarnn : ModelS ((L o i, L o o, R o, R o)) (R o) (R i) (R o) 
fcarnn (BV (wX,wS,wSm,b)) (BV x) (BV s) = let y = (wX #> x + wS #> s + b) * wSm
                                          in  (BV y, BV $ logistic <$> y)

fcarnn' : {o:_} -> ModelS (L o i, L o o, R o, R o) (R o) (R i) (R o)
fcarnn' p x s with (out4 p)
  _ | (wX,wS,wSm,b) = let y = (wX #> x + wS #> s + b) * wSm
                      in  (y, logistic <$> y)

infixr 8 <*~*
(<*~*)
  : (Backprop p, Backprop q, Backprop s, Backprop t)
    => ModelS  p     s    b c
    -> ModelS    q     t  a b
    -> ModelS (p,q) (s,t) a c
(f <*~* g) (BV (p, q)) x (BV (s, t)) =
  let (y, BV t') = g (BV q) x (BV t)
      (z, BV s') = f (BV p) y (BV s)
  in (z, BV (s', t'))

infixr 8 <*~
(<*~)
   : (Backprop p, Backprop q)
    => Model   p         b c
    -> ModelS       q  s a b
    -> ModelS (p,   q) s a c
(f <*~ g) (BV (p, q)) x = mapFst (f (BV p)) . g (BV q) x

mapS : (forall z. Ref z W => AD' z b -> AD' z c)
    -> ModelS p s a b
    -> ModelS p s a c
-- mapS g f s a b = let (z,s') = f s a b in (g z,s')
mapS f g p x = mapFst f . g p x

toS : Model p a b -> ModelS p s a b
toS f p x s = (f p x, s)

feedForwardLog
    : Model (L o i, R o) (R i) (R o)
feedForwardLog (BV (w, b)) (BV x) = BV $ map logistic (w #> x + b)

-- feedForwardLog' : Model (L o i, R o) (R i) (R o)

-- twoLayerRNN : ModelS _ (R 5,R 5) (R 20) (R 5)
-- _ isn't good enough, we need to search via ?
-- i, used here, is the hidden layers of the model
twoLayerRNN : ModelS ? ? (R 20) (R 5)
twoLayerRNN = fcrnn {i=10} <*~* mapS (map logistic) fcrnn

-- i, used here, is the hidden layers of the model
threeLayerRNN : ModelS ? ? (R 20) (R 5)
threeLayerRNN = fcrnn {i=10} <*~* mapS (map logistic) (fcrnn {i=20}) <*~* mapS (map logistic) fcrnn

hybrid : ModelS ? ? (R 40) (R 10)
hybrid = feedForwardLog {i=20}
         <*~  mapS (map logistic) (fcrnn {i=20})
         <*~* mapS (map logistic) fcrnn

unroll : ModelS p s a b -> ModelS p s (List a) (List b)
unroll = ?dssffd

-}