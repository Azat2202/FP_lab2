module HashMap

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
  slots: Vect size (Entry a)

%name Entry en
%name HashMap hm

emptyHashMap : (Hashable a) => Nat -> HashMap a
emptyHashMap k = MkHashMap k (replicate k Empty)

get_idx : (Hashable a) => a -> Nat -> Nat
get_idx x Z     = Z
get_idx x (S k) = (hash x) `mod` (S k) 

get_iteration_indexes : (size: Nat) -> Nat -> List (Fin size)
get_iteration_indexes size idx = let (before, after) = splitAt idx (allFins size) in after ++ before

replaceAt : Fin len -> elem -> (list : List elem) -> List elem
replaceAt _      y []      = []
replaceAt FZ     y (x::xs) = y :: xs
replaceAt (FS k) y (x::xs) = x :: replaceAt k y xs

insert : (Hashable a) => a -> HashMap a -> Maybe (HashMap a)
insert item (MkHashMap size slots) = 
   let idx = get_idx item size 
     in go (get_iteration_indexes size idx) where
        go : List (Fin size) -> Maybe (HashMap a)
        go [] = Nothing
        go (x :: xs) = case index x slots of
                            Empty => Just $ MkHashMap size (replaceAt x (Just item 1) slots)
                            (Just entry count) => case entry == item of
                                                    False => go xs 
                                                    True  => Just $ MkHashMap size (replaceAt x (Just item (S count)) slots)

delete : (Hashable a) => a -> HashMap a -> Maybe (HashMap a)
delete _    (MkHashMap Z    _    ) = Nothing
delete item (MkHashMap size slots) = 
  let idx = get_idx item size in 
      go (get_iteration_indexes size idx) where
        go : List (Fin size) -> Maybe (HashMap a)
        go [] = Nothing
        go (x :: xs) = case index x slots of
                            Empty => Nothing
                            (Just entry Z) => Just $ MkHashMap size (replaceAt x Empty slots)
                            (Just entry (S count)) => if entry /= item then go xs else
                                                      if count == Z 
                                                         then Just $ MkHashMap size (replaceAt x Empty slots)
                                                         else Just $ MkHashMap size (replaceAt x (Just entry count) slots)

filter : (Hashable a) => (a -> Bool) -> HashMap a -> HashMap a
filter f (MkHashMap size slots) = case filter filter_entry slots of
                                          ((len ** new_slots)) => MkHashMap len new_slots
                                          where 
                                            filter_entry : (Entry a -> Bool)
                                            filter_entry Empty = False
                                            filter_entry entry@(Just x k) = f x 


