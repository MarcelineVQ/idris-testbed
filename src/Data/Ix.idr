module Data.Ix

-- The Ix typeclass, for specifying indices and ranges of datatypes

-- Shape : Type -> Type

-- interface Ord a => Ix a where
  -- 0 Shape : Type -> Type
  -- range : Shape x -> List x
  -- inRange : Shape x -> x -> Bool
  -- index : Shape x -> x -> Int -- Not really Int, (Shape - 1)


interface Ord b => Ix b where
  range : (b,b) -> List b
  inRange : (b,b) -> b -> Bool
  index : (b,b) -> b -> Maybe Int

Ix Int where
  range (x,y) = [x..y]
  inRange (x,y) i = if x <= i && i <= y then True else False
  index b@(x,y) i = if inRange b i then Just (i - x) else Nothing

(Ix a, Ix b, Ord a) => Ix (a,b) where
  range ((x,y),(x',y')) = [ (i,i') | i <- range (x,x'), i' <- range (y,y')]
  inRange (x,y) i = ?fwefwef -- if i >= x && i <= y then True else False
  index b@(x,y) i = ?fwefw12ef -- if inRange b i then Just (i - x) else Nothing




