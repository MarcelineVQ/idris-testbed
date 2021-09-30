module Data.ArrayFire.Num

import Data.ArrayFire

%inline
wrapAPIFunc : (func : String) -> (msg : String) -> IO (Either AFErr a) -> a
wrapAPIFunc func msg act = 
  either (\_ => believe_me "wrapAPIFailure") id (unsafePerformIO act)

sum : AFArray dims dt -> Double
sum arr = Num.wrapAPIFunc "afSumAll" "sum" $ afSumAll arr

{ty:_} -> {dims:_} -> Num (AFArray dims ty) where
  x + y = Num.wrapAPIFunc "AFArrayNum" "+" $ afAdd x y
  x * y = Num.wrapAPIFunc "AFArrayNum" "*" $ afMul x y
  fromInteger x = unsafePerformIO $ pure (Num.wrapAPIFunc "AFArrayNum" "fromInteger" $ afConstant _ _ (fromInteger x))

-- (fromInteger 1) is being lifted to (csegen-18) function, an an issue arises thus?
-- (fromInteger 0) does not have this issue
-- if both are (fromInteger 0) though the issue arises, so it's a lifting problem
-- this is perhaps the issue all along everywhere for me?
main : IO ()
main = do
  let d = sum {dt=F64} {dims=[200,200]} $ foldr (+) (Num.fromInteger 1) (replicate 100 (Num.fromInteger 1))
  printLn d
