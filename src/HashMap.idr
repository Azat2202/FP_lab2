module HashMap

import Data.Vect
import Utils.Hashable

%default total


-- data HashMap : a -> Type where
  -- MkHashMap : (Hashable a) => (size: Nat) -> (capacity: Nat) -> (slots: Vect capacity (Maybe a)) -> HashMap a 

record HashMap a where
  constructor MkHashMap
  capacity : Nat
  size : Fin (S capacity)
  slots : Vect capacity (Maybe a)

%name HashMap hm

emptyHashMap: (Hashable a) => (capacity: Nat) -> HashMap a
emptyHashMap capacity = MkHashMap capacity FZ (replicate capacity Nothing)

get_idx: (Hashable a) => a -> (capacity: Nat) -> Fin capacity
get_idx x Z = ?todo
get_idx x capacity@(S k) = case natToFin (modNatNZ (hash x) capacity SIsNonZero) capacity of
                       Nothing => FZ
                       Just a => a


isLast: Fin (S n) -> Bool
isLast FZ = False
isLast (FS FZ) = True
isLast (FS (FS k)) = isLast (FS k)

finSElseZ: Fin n -> Fin n 
finSElseZ Fin k = case k == n of 
                       True => FZ 
                       False => finS x

                  

||| Get index and map to insert and return Just a if the item is inserted and Nothing else
public export
insert: (Hashable a) => a -> (map: HashMap a) -> HashMap a
insert x hm@(MkHashMap capacity size slots) = 
  let idx = get_idx x capacity in 
      insert_at_idx idx where
        insert_at_idx: Fin capacity -> HashMap a
        insert_at_idx idx' = 
          case index idx' slots of 
               Nothing => let new_slots = replaceAt idx' (Just x) slots in 
                              MkHashMap capacity size new_slots
               Just a => insert_at_idx (finS idx')


                 
