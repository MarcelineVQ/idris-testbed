module Oanda.Coda.Decode

import Oanda.Coda.Parser
import Generics.Derive

%language ElabReflection

public export
interface Decode t where
  constructor MkDecode
  decode : Parser t

public export
Decode Int where decode = mapMaybe parseInteger next

public export
Decode Double where decode = mapMaybe parseDouble next

public export
Decode Bool where
  decode = mapMaybe parseBool next
    where parseBool : String -> Maybe Bool
          parseBool "False" = Just False
          parseBool "True"  = Just True
          parseBool _       = Nothing

public export
Decode Nat where decode = mapMaybe parsePositive next

public export
Decode String where decode = next

||| First, the number of elements is decoded, followed
||| by a repeated application of the element Decoder.
public export
Decode a => Decode (List a) where
  decode = decode >>= repeat decode

public export
NP (Decode . f) ks => Decode (NP f ks) where
  decode = hsequence $ hcpure (Decode . f) decode

decodeCon :  forall ks . Decode (NP f ks)
          => ConInfo ks -> (toSOP : NP f ks -> SOP f kss) -> Parser (SOP f kss)
decodeCon ci toSOP = string ci.conName *> map toSOP decode

(decs : NP (Decode . f) ks) => SingletonList ks => Decode (NS f ks) where
  decode {decs = _ :: _ } = map Z decode

public export
POP (Decode . f) kss => Decode (POP f kss) where
  decode = map MkPOP decode

POP (Decode . f) kss => SingletonList kss => Decode (SOP f kss) where
  decode = map MkSOP decode

-- Generic decoding function
export
genDecode : {code : _} -> Meta t code => (all : POP Decode code) => Parser t
genDecode {all = MkPOP _} = to <$> decodeSOP (metaFor t)
  where decodeSOP : TypeInfo code -> Parser (SOP I code)
        decodeSOP (MkTypeInfo _ _ cons) =
          hchoice $ hcliftA2 (Decode . NP I) decodeCon cons injectionsSOP

-- genDecode :  Generic t code
--           => POP Decode code
--           => SingletonList code
--           => Parser t
-- genDecode = map to decode


||| Derives a `Decode` implementation for the given data type
||| and visibility.
DecodeVis : Visibility -> DeriveUtil -> InterfaceImpl
DecodeVis vis g = MkInterfaceImpl "Decode" vis []
                       `(MkDecode genDecode)
                       (implementationType `(Decode) g)

export
||| Alias for `DecodeVis Public`.
Decode' : DeriveUtil -> InterfaceImpl
Decode' = DecodeVis Public



export
data Spell = MkSpell Nat String

%runElab derive "Spell" [Generic, Meta, Eq, Ord, DecEq, Show, Decode']

export
data Monster : Type where
  Goblin   : (hp : Int) -> (name : String) -> Monster
  Demon    : (hp : Int) -> (sp : Int) -> (spells : List Spell) -> Monster
  Skeleton : (hp : Int) -> (armor : Int) -> Monster

%runElab derive "Monster" [Generic, Meta, Eq, Ord, DecEq, Show, Decode']

-- granularity is a mere string in oanda
public export
data Granularity = S5 | S10 | S15 | S30
                 | M1 | M2  | M4  | M5 | M10 | M15 | M30
                 | H1 | H2  | H3  | H4 | H6  | H8  | H12
                 | D  | W   | M

%runElab derive "Granularity" [Generic, Meta, Eq, Ord, Show, DecEq, Decode']

-- foofer : decode "M1" "M1M2M3" = Just M1
-- foofer = ?aSDFfs