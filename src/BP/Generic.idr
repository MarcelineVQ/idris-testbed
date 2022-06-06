module BP.Generic

import BP.Backprop

import Generics.Derive

%language ElabReflection

--- Derive backprop instances generically, no promises


-- n-ary products, e.g. (a,b,c)   (data Foo x y = MkFoo x y)
-- add just does pointwise combination
NP (Backprop . f) ks => Backprop (NP f ks) where
  zero = hcliftA (Backprop . f) zero
  one = hcliftA (Backprop . f) one
  add = hcliftA2 (Backprop . f) add

-- n-ary sums,  e.g. Either a b      (data Foo a b c = MkFoo1 a b | MkFoo2 b c)
-- I'm not sure what Backprop should mean for n-ary sums like Either, so we'll
-- restrict this to single constructor types for now.
public export
(all : NP (Backprop . f) [k']) => Backprop (NS f [k']) where
  -- encode = hconcat . hcmap (Encode . f) encode
  zero = hcliftA (Backprop . f) zero -- should this work?
  one = hcliftA (Backprop . f) one -- should this work?
  add {all = _::_} (Z x) (Z y) = Z $ x `add` y

public export
POP (Backprop . f) kss => Backprop (POP f kss) where
  zero (MkPOP nps) = MkPOP $ zero nps
  one (MkPOP nps) = MkPOP $ one nps
  add (MkPOP nps1) (MkPOP nps2) = MkPOP $ add nps1 nps2

public export
(all : POP (Backprop . f) [k']) => Backprop (SOP f [k']) where
  zero (MkSOP nps) = MkSOP $ zero nps
  one (MkSOP nps) = MkSOP $ one nps
  add (MkSOP nps1) (MkSOP nps2) = MkSOP $ add nps1 nps2

export
genericZero : Generic t [code] => POP Backprop [code] => t -> t
genericZero = to . zero . from

export
genericOne : Generic t [code] => POP Backprop [code] => t -> t
genericOne = to . one . from

export
genericAdd : Generic t [code] => POP Backprop [code] => t -> t -> t
genericAdd x y = to $ add (from x) (from y)

export
||| Derives a `Backprop` implementation for the given data type
||| and visibility.
BackpropVis : Visibility -> DeriveUtil -> InterfaceImpl
BackpropVis vis g = MkInterfaceImpl "Backprop" vis []
                       `(MkBackprop genericZero genericOne genericAdd)
                       (implementationType `(Backprop) g)

export
||| Alias for `EncodeVis Public`.
Backprop : DeriveUtil -> InterfaceImpl
Backprop = BackpropVis Public
