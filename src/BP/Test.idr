module BP.Test

import Hedgehog

import BP.Backprop

import Util

import BP.Generic

import Data.Stream -- cycle

import Control.Monad.Trans

import Numeric.Floating

import Generics.Newtype
%language ElabReflection

-- shouldn't actually be exported
%runElab derive "Pair"
  [Generic, Eq, Ord, Num, Neg, Abs, Fractional, FromDouble, Integral]

export
linReg : Num a => Backprop a => AD z (a, a) -> AD z a -> AD z a
linReg ab x with (out2 ab)
  _ | (b, y) = y * x + b
-- (-1 , 2.0)

export
linRegHarder : Neg a => Num a => Backprop a => AD z (a, a, a) -> AD z a -> AD z a
linRegHarder ab x with (mapSnd out2 (out2 ab))
  _ | (b, y, z') = y * x + b - z'
-- ^ many choices we got (-8.5, 2.0, -7.5) when running which is also (-1 , 2.0, 0.0)

linRegHarderer : Neg a => Num a => Backprop a => AD z (a, a, a, a) -> AD z a -> AD z a
linRegHarderer ab x with (mapSnd (mapSnd out2) (mapSnd out2 (out2 ab)))
  _ | (b, y, z', w) = y * x + b - z' * w

linRegHarderer' : Neg a => Num a => Backprop a => AD z (a, a, a, a) -> AD z a -> AD z a
linRegHarderer' ab x with (mapSnd (mapSnd out2) (mapSnd out2 (out2 ab)))
  _ | (b, y, z', w) = linReg (in2 z' w) (linReg (in2 b y) x)

linReg1 : Neg a => Num a => Backprop a => AD z (a, a) -> AD z a -> AD z a
linReg1 ab x with (out2 ab)
  _ | (a', b') = a' + b' + x

linReg2 : Neg a => Num a => Backprop a => AD z (a, a) -> AD z a -> AD z a
linReg2 ab x with (out2 ab)
  _ | (a', b') = a' - b' - x

linReg3 : Neg a => Num a => Backprop a => AD z (a, a) -> AD z a -> AD z a
linReg3 ab x with (out2 ab)
  _ | (a', b') = a' * b' * x

linReg1' : Neg a => Num a => Backprop a => AD z a -> AD z a -> AD z a
linReg1' ab x = ab + x

linReg2' : Neg a => Num a => Backprop a => AD z a -> AD z a -> AD z a
linReg2' ab x = ab - x

linReg3' : Neg a => Num a => Backprop a => AD z a -> AD z a -> AD z a
linReg3' ab x = ab * x

-- this causes NaN for no good reason, is in2 our baddie?
-- learning rate 0.00001 works, I seem to need exponentialy smaller training
-- rates when I combine linReg's.
-- Is this due to out2 or in2?
-- I do have a special out2...
-- Is this from mutating vars instead of immutable?
linReg4 : Neg a => Num a => Backprop a => AD z (a,a) -> AD z a -> AD z a
linReg4 ab x with (out2 ab)
  _ | (a', b') = linReg1 (in2 (linReg1 ab x) (linReg1 ab x)) x

reg4Data : List (Double,Double) -- (7,3)
reg4Data = [(1,23.0),(2,26.0),(3,29.0),(4,32.0),(5,35.0)]

linReg5 : Neg a => Num a => Backprop a => AD z (a,a) -> AD z a -> AD z a
linReg5 ab x = linReg3 ab x + linReg2 ab x + linReg1 ab x + x

reg5Data : List (Double,Double) -- (7,3)
reg5Data = [(1,36.0),(2,58.0),(3,80.0),(4,102.0),(5,124.0),(6,146.0),(7,168.0),(8,190.0),(9,212.0)]

linReg6 : Neg a => Num a => Backprop a => AD z a -> AD z a -> AD z a
linReg6 ab x = linReg3' ab (linReg3' ab x) + linReg2' ab (linReg2' ab x) + linReg1' ab (linReg1' ab x) + x
-- linReg6 demonstrates that nesting is at issue

reg6Data : List (Double,Double) -- 8
-- reg6Data = [(1,25.0),(2,34.0),(3,43.0),(4,52.0),(5,61.0),(6,70.0),(7,79.0),(8,88.0),(9,97.0),(10,106.0)]
reg6Data = [(1,83.0),(2,150.0),(3,217.0),(4,284.0),(5,351.0),(6,418.0),(7,485.0),(8,552.0),(9,619.0)]

export
linRegSamps : List (Double, Double)
linRegSamps = [(1,1),(2,3),(3,5),(4,7),(5,9)]

export
squaredErrorGrad : (Show a, Show b, Show p, Backprop p, Backprop b, Num a, Num b, Neg b, Floating b)
    => (forall z. AD z p -> AD z a -> AD z b)      -- ^ Model
    -> a                -- ^ Observed input
    -> b                -- ^ Observed output
    -> p                -- ^ Parameter guess
    -> p                -- ^ Gradient
squaredErrorGrad f x targ = gradBP $ \p => (f p (auto' x) - auto' targ) ^ 2

export
trainModel
     : Backprop p
    => Show a
    => Show b
    => Show p
    => Num b
    => Num a
    => Neg b
    => FromDouble p
    => Neg p
    => Floating b
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
    => Show a
    => Show b
    => Show p
    => Num b
    => Num a
    => Neg b
    => FromDouble p
    => Floating b
    => Neg p
    => Backprop b
    => p -- learningrate
    -> (forall z. AD z p -> AD z a -> AD z b)      -- ^ model to train
    -> p                -- ^ initial parameter guess
    -> List (a,b)          -- ^ list of observations
    -> List (p)                -- ^ updated parameter guess
trainModel' r f = scanl $ \p,(x,y) => p - r * squaredErrorGrad f x y p

export
linRegTest : (Double, Double) -> (Double, Double)
linRegTest s =
  trainModel 0.01 linReg s (take 5000 $ cycle [(1,1),(2,3),(3,5),(4,7),(5,9),(6,11),(7,13),(8,15),(9,17)])

hardererData : List (Double,Double)
hardererData = [(1,-35),(2,-33),(3,-31),(4,-29),(5,-27),(6,-25),(7,-23),(8,-21),(9,-19),(10,-17)]

double10 : Gen Double
double10 = double $ constant (-10) 10

closeEnough : Double -> Double
closeEnough d = let modi = 1000
                    d' = d * cast modi
                in cast . (`div`modi) . cast {to=Integer} $ d'

bothCloseEnough : (Double, Double) -> (Double, Double)
-- bothCloseEnough = bimap closeEnough closeEnough
bothCloseEnough = bimap round round

allCloseEnough : (Double, Double, Double) -> (Double, Double, Double)
-- bothCloseEnough = bimap closeEnough closeEnough
allCloseEnough = bimap round (bimap round round)

fof : (Double,Double,Double) -> (Double,Double)
fof (x,y,z) = (x-z,y)

-- evalBP instead of gradbp to get test data

propTwice2 : Property
propTwice2 = withTests 100 . property $
                do n <- forAll double10
                   m <- forAll double10
                   zed <- forAll double10
                   bothCloseEnough (trainModel 0.01 linReg (n,m) (take 5000 $ cycle [(1,1),(2,3),(3,5),(4,7),(5,9),(6,11),(7,13),(8,15),(9,17)]))
                     === ((-1.0), 2.0)
                   bothCloseEnough (fof $ trainModel 0.01 linRegHarder (n,m,zed) (take 5000 $ cycle [(1,1),(2,3),(3,5),(4,7),(5,9),(6,11),(7,13),(8,15),(9,17)]))
                     === ((-1.0), 2.0)
                   -- bothCloseEnough (linRegTest (n, m)) === ((-1.0), 2.0)

export
checkTwice2 : IO Bool
checkTwice2 = checkNamed "propTwice2" propTwice2


main : IO ()
main = pure ()