module Utils.Hashable

%default total

public export
interface Eq a => Hashable a where
  hash: a -> Nat

public export 
Hashable Int where
  hash a = cast a

public export 
Hashable Integer where
  hash a = cast a

public export
Hashable String where 
  hash a = integerToNat $ cast $ sum $ map ord (unpack a)


h: Nat -> Nat
h 0 = 0
h (S k) = case k of
               0 => ?h_rhs_2
               (S j) => ?h_rhs_3
