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

Functor HashMap where 
  map f (MkHashMap size slots) = MkHashMap size (map f_entry slots) 
                                  where 
                                    f_entry : (Entry a -> Entry b)
                                    f_entry Empty = Empty
                                    f_entry (Just x k) = Just (f x) k
namespace Foldr
  repeat : (t -> acc -> acc) -> (acc -> acc) -> Entry t -> (acc -> acc)
  repeat f go Empty          = go
  repeat f go (Just x 0    ) = go
  repeat f go (Just x (S k)) = assert_total $ repeat f (go . (f x)) (Just x k)
  
  export
  foldrImpl : (t -> acc -> acc) -> acc -> (acc -> acc) -> HashMap t -> acc
  foldrImpl f e go (MkHashMap 0       []     ) = go e
  foldrImpl f e go (MkHashMap (S len) (x::xs)) = assert_total $ foldrImpl f e (go . (repeat f id x)) (MkHashMap len xs)

namespace Foldl
  repeat : (a -> acc -> acc) -> acc -> Entry a -> acc
  repeat f acc Empty          = acc
  repeat f acc (Just y 0    ) = acc
  repeat f acc (Just y (S k)) = assert_total $ repeat f (f y acc) (Just y k)

  export
  foldlImpl : (a -> acc -> acc) -> acc -> HashMap a -> acc
  foldlImpl f x (MkHashMap 0       []       ) = x
  foldlImpl f x (MkHashMap (S len) (y :: xs)) = assert_total $ foldlImpl f (repeat f x y) (MkHashMap len xs)

Foldable HashMap where 
  foldr f acc hm = Foldr.foldrImpl f acc id hm
  foldr f acc hm = Foldl.foldlImpl f acc hm 

Show a => Show (Entry a) where
  show Empty = "Empty"
  show (Just x k) = "(" ++ (show x) ++ ")x" ++ (show k) 

Show a => Show (HashMap a) where
  show (MkHashMap size slots) = "HashMap, size: " ++ (show size) ++ "elements: " ++ (show slots)
