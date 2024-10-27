module HashMap

import Data.List
import Data.Vect
import Data.Fin
import Utils.Hashable

%default total

record HashMap a where
  constructor MkHashMap
  capacity: Nat
  size: Nat
  slots: Vect size (Maybe a)

%name HashMap hm

emptyHashMap : (Hashable a) => Nat -> HashMap a
emptyHashMap k = MkHashMap Z k (replicate k Nothing)

get_idx : (Hashable a) => a -> Nat -> Nat
get_idx x Z = Z
get_idx x (S k) = (hash x) `mod` (S k) 

get_iteration_indexes : (size: Nat) -> Nat -> List (Fin size)
get_iteration_indexes size idx = let (before, after) = splitAt idx (allFins size) in after ++ before

replaceAt : Fin len -> elem -> (list : List elem) -> List elem
replaceAt _     y []      = []
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

insert : (Hashable a) => a -> HashMap a -> Maybe (HashMap a)
insert item (MkHashMap capacity size slots) = 
  case isLT capacity size of
    (No contra) => Nothing
    (Yes prf) => let idx = get_idx item size 
      in go (get_iteration_indexes size idx) where
        go : List (Fin size) -> Maybe (HashMap a)
        go [] = Nothing
        go (x :: xs) = case index x slots of
                            (Just y) => go xs
                            Nothing => Just $ MkHashMap (S capacity) size (replaceAt x (Just item) slots)


