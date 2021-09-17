module Data.JSON.Array

import Data.Strong.Array

import Decidable.Equality
import JSON
import Generics.Derive
%language ElabReflection

export
ToJSON a => ToJSON (Array s a) where
  toJSON = toJSON . toList

export
FromJSON a => FromJSON (s : Nat ** Array s a) where
  fromJSON = map fromList' . fromJSON

export
{s:_} -> FromJSON a => FromJSON (Array s a) where
  fromJSON x = do
    xs <- fromJSON {a=List a} x
    case decEq (length xs) s of
      (No contra) => fail "List length not correct, expected \{show s} got \{show (length xs)}"
      (Yes Refl) => Right $ fromList xs
