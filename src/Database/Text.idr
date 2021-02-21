module Database.Text

-- basic-ass text-file-as-db

import Data.List
import Data.SnocList
import Data.String

import System.File

public export
record TimeStamp where
  constructor MkTimeStamp
  -- seconds : Integer
  -- minutes : Integer
  -- hours : Integer
  -- timezone : TimeZone
  unixTime : Double
  -- Seconds since the Unix Epoch (January 1st, 1970 at UTC). The value is a
  -- fractional number, where the fractional part represents a fraction of a
  -- second (up to nine decimal places).

export
Show TimeStamp where
  show (MkTimeStamp t) = show t

export
Cast String TimeStamp where
  cast = MkTimeStamp . cast {to=Double}

export
FromDouble TimeStamp where
  fromDouble = MkTimeStamp . fromDouble

-- real entry should have bid and ask versions of each of these, and also tick size

-- An entry of a closed candle
public export
record Entry where
  constructor MkEntry
  cTime : TimeStamp -- candle close time
  cOpen : Double
  cClose : Double
  cHigh : Double
  cLow : Double

export
Show Entry where
  showPrec p (MkEntry cTime cOpen cClose cHigh cLow) = showCon p "MkEntry" $ showArg cTime ++ showArg cOpen ++ showArg cClose ++ showArg cHigh ++ showArg cLow

public export
data Zipper a = MkZipper (SnocList a) a (List a)

export
Show a => Show (Zipper a) where
  showPrec p (MkZipper sx x xs) = showCon p "MkZipper" $ showArg sx ++ showArg x ++ showArg xs

export
moveLeft : Zipper a -> Zipper a
moveLeft (MkZipper (sx :< y) x xs) = MkZipper sx y (x :: xs)
moveLeft zip = zip

export
moveRight : Zipper a -> Zipper a
moveRight (MkZipper sx y (x :: xs)) = MkZipper (sx :< y) x xs
moveRight zip = zip


export
allRight : Zipper a -> Zipper a
allRight z = case moveRight z of
               zip@(MkZipper _ _ []) => zip
               zip => allRight zip

export
allLeft : Zipper a -> Zipper a
allLeft z = case moveLeft z of
              zip@(MkZipper [<] _ _) => zip
              zip => allLeft zip

export
addLeft : a -> Zipper a -> Zipper a
addLeft x (MkZipper sx y xs) = MkZipper sx x (y :: xs)

export
addRight : Zipper a -> a -> Zipper a
addRight (MkZipper sx y xs) x = MkZipper (sx :< y) x xs

-- requires an empty Zipper case

export
viewLeft : Zipper a -> (Maybe (Zipper a), a)
viewLeft (MkZipper [<] y []) = (Nothing, y)
viewLeft (MkZipper [<] y (x :: xs)) = (Just $ MkZipper [<] x xs, y)
viewLeft (MkZipper (sx :< x) y xs) = (Just $ MkZipper sx x xs, y)

export
viewRight : Zipper a -> (Maybe (Zipper a), a)
viewRight (MkZipper [<] y []) = (Nothing, y)
viewRight (MkZipper (sx :< x) y []) = (Just $ MkZipper sx x [], y)
viewRight (MkZipper sx y (x :: xs)) = (Just $ MkZipper sx x xs, y)

export
readZipper : Zipper a -> a
readZipper (MkZipper _ x _) = x

export
Cast (Zipper a) (List a) where
  cast from = case allLeft from of
                (MkZipper _ x xs) => x :: xs

export
Functor Zipper where
  map f (MkZipper sx x xs) = MkZipper (map f sx) (f x) (map f xs)

-- might be more efficient to fold each component, to avoid traversing twice
export
Foldable Zipper where
  foldr f acc zip = case allLeft zip of
    (MkZipper _ x xs) => f x (foldr f acc xs)

export
Traversable Zipper where
  traverse f (MkZipper sx x xs) = [| MkZipper (traverse f sx) (f x) (traverse f xs) |]



data IZipper : Nat -> Nat -> Type -> Type where
  MkIZipper :  SnocList a -> a -> List a -> IZipper m n a

sliceZipper : (i : Nat) -> (j : Nat) -> IZipper m n a -> IZipper (min m i) (min n j) a


export
saveEntry : Entry -> String
saveEntry (MkEntry cTime cOpen cClose cHigh cLow) =
  (concat $ intersperse "," [show cTime, show cOpen, show cClose, show cHigh, show cLow]) ++ "\n"

export
loadEntry : String -> Maybe Entry
loadEntry str = case sep (unpack str) of
    [t,o,c,h,l] => Just $ MkEntry (cp t) (cp o) (cp c) (cp h) (cp l)
    _ => Nothing
  where
    cp : Cast String b => List Char -> b
    cp = cast . pack
    sep : List Char -> List (List Char)
    sep s = case dropWhile (==',') s of
                [] => []
                s' => let (w, s'') = break (==',') s'
                      in w :: sep s''

export
save : HasIO io => (fileName : String) -> Zipper Entry -> io (Either FileError ())
save fileName x = do
  let z = cast {to=List Entry} x
      d = concatMap saveEntry z
  writeFile fileName d

export
load : HasIO io => (fileName : String) -> io (Either FileError (Zipper Entry))
load fileName = do
  Right c <- readFile fileName
    | Left err => pure (Left err)
  Just (r :: res) <- pure $ traverse loadEntry (lines c)
    | _ => pure $ Left $ GenericFileError 69
  pure $ Right $ MkZipper [<] r res



export
main : IO ()
main = pure ()
