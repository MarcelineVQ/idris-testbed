module Data.Strong.Array.Fusion

import Data.Strong.Array



-- %hide Prelude.Basics.(.)

-- data Step : Type -> Type -> Type where
--   Yield : a -> s -> Step s a
--   Skip : s -> Step s a
--   Done : Step s a
-- 
-- data Stream : Nat -> Type -> Type where
--   MkStream : (s -> Step s a) -> s -> (n : Nat) -> Stream n a
-- 
-- stream : Array n a -> Stream n a
-- stream arr = case arr of
--     MkArray s _ _ => MkStream step 0 s
--   where
--     step : Int -> Step Int a
--     step s = if s >= intSize arr
--       then Done
--       else Yield (unsafeReadArray arr (cast s)) (s+1)
-- 
-- -- dot : (b -> c) -> (a -> b) -> (a -> c)
-- -- dot f g x = f (g x)
-- 
-- unstream : Stream n a -> Array n a
-- unstream (MkStream step s' max) = inewArrayFill max (\_ => step' s')
--   where
--     step' : forall s. s -> a
-- 
-- mapS : (a -> b) -> Stream n a -> Stream n b
-- mapS f (MkStream step s i) = MkStream (\s' => case step s' of
--   (Yield x y) => Yield (f x) y
--   (Skip x) => Skip x
--   Done => Done) s i
-- 
-- infixr 9 `bip`
-- export
-- bip : (b -> c) -> (a -> b) -> a -> c
-- bip f g = \x => f (g x)


-- these work
-- %transform "what" Prelude.(.) = Fusion.bip
-- %transform "what2" Fusion.bip = Prelude.(.)

-- transforms fire before inlining, so this is pointless anyway, even if it
-- worked as intended map' won't have a stream . unstream in the middle to
-- remove
-- %transform "vectStreamFusion" Fusion.stream . Fusion.unstream = Prelude.id

-- What if we instead use a builder pattern


data Step : Type -> Type -> Type where
  Yield : a -> s -> Step s a
  Skip : s -> Step s a
  Done : Step s a
  ||| Fusion constructor
  ||| We don't have a serious rewrite system in idris2 yet so this does the job
  ||| of fusing as long as we're careful about using streamFold and Build
  ||| whenever we can.
  Build : (forall b. (a -> s -> b) -> (s -> b) -> b -> b) -> Step s a


-- data Stream : Nat -> Type -> Type where
  -- MkStream : (s -> Step s a) -> s -> (n : Nat) -> Stream n a


export
streamBuild : (forall b. (a -> s -> b) -> (s -> b) -> b -> b)
           -> Step s a
streamBuild = \phi => phi Yield Skip Done

export
streamFold : (a -> s -> b) -> (s -> b) -> b -> Step s a -> b
streamFold y s r (Yield x z) = y x z
streamFold y s r (Skip x) = s x
streamFold y s r Done = r
streamFold y s r (Build f) = f y s r



streamStep : Array n a -> Int -> Step Int a
streamStep arr i = case arr of
    MkArray _ is _ => if i >= is
      then Done
      else Yield (unsafeReadArray arr (cast i)) (i+1)

data Stream : Nat -> Type -> Type where
  MkStream : (s -> Step s a) -> s -> (n : Nat) -> Stream n a

-- stream : Array n a -> Stream n a
-- stream arr = case arr of
--     MkArray s _ _ => MkStream step 0 s
--   where
--     step : Int -> Step Int a
--     step s = if s >= intSize arr
--       then Done
--       else Yield (unsafeReadArray arr (cast s)) (s+1)
-- 
-- -- dot : (b -> c) -> (a -> b) -> (a -> c)
-- -- dot f g x = f (g x)
-- 
-- unstream : Stream n a -> Array n a
-- unstream (MkStream step s' max) = inewArrayFill max (\_ => step' s')
--   where
--     step' : forall s. s -> a


-- dot : (b -> c) -> (a -> b) -> (a -> c)
-- dot f g x = f (g x)

-- unstream : Stream n a -> Array n a
-- unstream (MkStream step s' max) = inewArrayFill max (\_ => step' s')
  -- where
    -- step' : forall s. s -> a

-- export
-- -- %inline
-- nak : Stream n a -> Stream n a
-- nak = stream `bip` unstream

-- export
-- nak2 : Stream n a -> Stream n a
-- nak2 = stream . unstream

-- export
-- nak3 : List Nat -> List Nat
-- nak3 = map (+1)
-- 
-- %inline
-- export
-- map' : (f : (a -> b)) -> Array s a -> Array s b
-- map' f =  unstream `bip` (nak2 . mapS f) `bip` stream
-- -- 
-- -- -- %inline
-- export  
-- blar : Array s Double -> Array s Double 
-- blar = map' (+1) `bip` map' (+2)

-- %transform "vectStreamFusion3" Fusion.map' f . Fusion.map' g = Fusion.map' (f . g)
 
main : IO ()
main = pure ()
-- main = do
  -- let xvar = nak $ MkStream {a=Int} (\_ => Done) 'a' 1
  -- printLn (blar $ fromList [1.0,2.0,3.0])
