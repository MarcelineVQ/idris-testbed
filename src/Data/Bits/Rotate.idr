module Data.Bits.Rotate

public export
interface RBit a where
  0 Index : Type
  rotateL : a -> Index -> a
  rotateR : a -> Index -> a


