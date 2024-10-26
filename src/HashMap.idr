module HashMap

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

const_range : (size: Nat) -> Vect size (Fin size)
const_range size = Data.Vect.Fin.range {len = size} 


insert : (Hashable a) => a -> HashMap a -> Maybe (HashMap a)
insert x (MkHashMap capacity (S size) slots) = 
  case isLT (S capacity) size of
    (No contra) => Nothing
    (Yes prf) => let idx = get_idx x size in 
                     let new_slots = try_insert (?get_iteration_indeciess idx) in 
                         ?huemoe where 
                       get_iteration_indecies : Nat -> Vect size (Fin size) 
                       get_iteration_indecies k = 
                        let (before, after) = splitAt k (const_range (S size)) in ?df

                       try_insert: Vect size (Fin size) -> Maybe (Vect size (Maybe a))
