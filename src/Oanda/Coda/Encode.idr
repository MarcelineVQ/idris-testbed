module Oanda.Coda.Encode

import Oanda.Coda.Parser
import Generics.Derive

%language ElabReflection



public export
interface Encode t where
  constructor MkEncode
  encode : t -> List String

public export
Encode Int where encode = pure . show

public export
Encode Double where encode = pure . show

public export
Encode Bool where encode = pure . show

public export
Encode Nat where encode = pure . show . cast {to = Integer}

public export
Encode String where encode = pure

||| Encoded lists are prefixed with an ecoding of
||| the number of elements
public export
Encode a => Encode (List a) where
  encode as = encode (length as) ++ concatMap encode as
--------------------------------------------------
public export
NP (Encode . f) ks => Encode (NP f ks) where
  encode = hconcat . hcmap (Encode . f) encode


encodeCon : Encode (NP f ks) => ConInfo ks -> NP f ks -> List String
encodeCon ci np = ci.conName :: encode np

NP (Encode . f) ks => SingletonList ks => Encode (NS f ks) where
  encode = hconcat . hcmap (Encode . f) encode

-- try turning this into a sum type decoder
-- NP (Encode . f) ks => SingletonList ks => Encode (NS f ks) where
  -- encode = hconcat . hcmap (Encode . f) encode

public export
POP (Encode . f) kss => Encode (POP f kss) where
  encode (MkPOP nps) = encode nps

POP (Encode . f) kss => SingletonList kss => Encode (SOP f kss) where
  encode (MkSOP v) = encode v

export
genEncode : Meta t code => (all : POP Encode code) => t -> List String
genEncode {all = MkPOP _} = encodeSOP (metaFor t) . from
  where encodeSOP : TypeInfo code -> SOP I code -> List String
        encodeSOP (MkTypeInfo _ _ cons) =
          hconcat . hcliftA2 (Encode . NP I) encodeCon cons . unSOP

-- genEncode :  Generic t code
--           => POP Encode code
--           => SingletonList code -- SingletonList means only 1-constructor
--           => t -> List String
-- genEncode = encode . from

EncodeVis : Visibility -> DeriveUtil -> InterfaceImpl
EncodeVis vis g = MkInterfaceImpl "Encode" vis []
                       `(MkEncode genEncode)
                       (implementationType `(Encode) g)
export
Encode' : DeriveUtil -> InterfaceImpl
Encode' = EncodeVis Public

data Spell = MkSpell Nat String
%runElab derive "Spell" [Generic, Meta, Eq, Ord, DecEq]

Encode Spell where encode = genEncode

||| The result can't be reduced any further, since `show` and
||| `cast` of primitives is involved.
encodeSpellTest : encode (MkSpell 10 "foo") =
                  ["MkSpell", show (cast {from = Nat} {to = Integer} 10), "foo"]
encodeSpellTest = Refl

||| Derives an `Encode` implementation for the given data type
||| and visibility.
-- EncodeVis : Visibility -> DeriveUtil -> InterfaceImpl
-- EncodeVis vis g = MkInterfaceImpl "Encode" vis []
--                        `(MkEncode genEncode)
--                        (implementationType `(Encode) g)
-- 
-- ||| Alias for `EncodeVis Public`.
-- Encode' : DeriveUtil -> InterfaceImpl
-- Encode' = EncodeVis Public


data DateTime : Type where
  MkDT : Double -> DateTime

%runElab derive "DateTime" [Generic, Meta, Eq, Ord, Show, Encode']

-- granularity is a mere string in oanda
public export
data Granularity = S5 | S10 | S15 | S30
                 | M1 | M2  | M4  | M5 | M10 | M15 | M30
                 | H1 | H2  | H3  | H4 | H6  | H8  | H12
                 | D  | W   | M

%runElab derive "Granularity" [Generic, Meta, Eq, Ord, Show, DecEq, Encode']

encodeGranTest : encode M5 =
                  ["M5"]
encodeGranTest = Refl