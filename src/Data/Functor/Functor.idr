module Data.Functor.Functor

infixr 9 ~>

data Free : (Type -> Type) -> Type -> Type where
  Pure : a -> Free f a
  Free' : f (Free f a) -> Free f a

Functor f => Functor (Free f) where
  map f (Pure x) = Pure (f x)
  map f (Free' x) = Free' $ map (map f) x

Applicative f => Applicative (Free f) where
  pure a = Pure a
  (Pure x) <*> fa = map x fa
  (Free' x) <*> xs = Free' $ (<*>) <$> x <*> pure xs

Applicative f => Monad (Free f) where
  (Pure x) >>= f = f x
  (Free' x) >>= f = Free' $ map (>>= f) x

-- natural transformation
(~>) : (Type -> Type) -> (Type -> Type) -> Type
f ~> g =  {-forall x.-} {x:_} -> f x -> g x

public export
interface HFunctor (t : (Type -> Type) -> Type -> Type) where
  hmap : (f ~> g) -> t f a -> t g a
  -- law: hmap id = id
  inject : f ~> t f

-- interface MonoidIn (t : (Type -> Type) -> (Type -> Type) -> Type -> Type) (i : Type) (f : Type -> Type) where

interface SemigroupIn tt (i : Type) f where
  binterpret : (g ~> f) -> h ~> f -> (tt g h ~> f)

interface SemigroupIn tt i f => MonoidIn tt i f where
  bzero : (tt g h ~> f)

public export
interface HBifunctor (tt : (Type -> Type) -> (Type -> Type) -> Type -> Type) where
  hbimap : (f ~> h) -> (g ~> j) -> tt f g a -> tt h j a
  -- law: bimap id id = id

inL : MonoidIn t i f => f ~> t f g
inR : MonoidIn t i g => g ~> t f g

fraf : {t:_} -> HFunctor t => t Maybe Char -> Int
fraf b = let c = hmap ?dsffds b in 3

interface Interpret (t : (Type -> Type) -> Type -> Type) (f : Type -> Type) where
  interpret : (g ~> f) -> (t g ~> f)

interpret' : {a:_} -> Interpret Free f => Monad g => (g ~> f) -> Free g a -> f a
interpret' r (Pure y) = r (pure y)
interpret' r (Free' y) = r (y >>= \z => ?dsff)

-- {f:_} -> Monad f => Interpret Free f where
  -- interpret r (Pure y) = r ?dsfdsf --(pure y)
  -- interpret r (Free' y) = ?dsfdsf_2

