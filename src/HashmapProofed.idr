module HashmapProofed

import Data.List
import Data.Vect
import Data.Fin
import Utils.Hashable

%default total

data Entry a = Empty 
             | Just a Nat 

record HashMap a where
  constructor MkHashMap
  size: Nat
  slots: Vect size (Entry (Hashable a))

%name Entry en
%name HashMap hm

emptyHashMap : Hashable a -> HashMap a
emptyHashMap k = MkHashMap k (replicate k Empty)

get_idx : Hashable a -> Nat -> Nat
get_idx x Z     = Z
get_idx x (S k) = (hash x) `mod` (S k) 

get_iteration_indexes : (size: Nat) -> Nat -> List (Fin size)
get_iteration_indexes size idx = let (before, after) = splitAt idx (allFins size) in after ++ before

replaceAt : Fin len -> elem -> (list : List elem) -> List elem
replaceAt _      y []      = []
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

mutual
  insert : Hashable a -> HashMap a -> HashMap a
  insert item hm@(MkHashMap size slots) = 
    let idx = get_idx item size 
       in go (get_iteration_indexes size idx) where
          go : List (Fin size) -> HashMap a
          -- We can assert_total because if we expand hashmap there will be one more Empty slot
          go [] = assert_total $ insert item (expand hm)
          go (x :: xs) = case index x slots of
                              Empty => MkHashMap size (replaceAt x (Just item 1) slots)
                              (Just entry count) => case entry == item of
                                                      False => go xs 
                                                      True  => MkHashMap size (replaceAt x (Just item (S count)) slots)

  insert_all : (Hashable a) => Vect size (Entry a) -> HashMap a -> HashMap a
  insert_all [] hm = hm
  insert_all (Empty :: xs) hm = insert_all xs hm
  insert_all ((Just x 0) :: xs) hm = insert_all xs hm
  insert_all prev_slots@((Just x (S k)) :: xs) hm = 
    insert_all (assert_smaller prev_slots (((Just x k)) :: xs)) (insert x hm)

  insert_all_values : (Hashable a) => Vect size a -> HashMap a -> HashMap a
  insert_all_values xs hm = insert_all (map (\e => Just e 1) xs) hm

  expand : (Hashable a) => HashMap a -> HashMap a
  expand {a} hm@(MkHashMap size slots) = let new_hm = emptyHashMap (size * 2) {a=a} in 
                                         insert_all slots new_hm

