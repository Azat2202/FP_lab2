module Main

import System
import Control.App
import Utils.Unit
import Tests

tests : List (Test es)
tests = [ empty_hm_k
        , empty_hm_Z
        , insert_no_shrink
        , insert_repeat_no_shrink
        , check_hashing
        , insert_all_test
        , insert_shrink
        , delete_found
        , delete_not_found
        , filter_test
        , map_test
        , map_with_hash_test
        , foldr_impl_test
        , foldl_impl_test
        ]

main : IO ()
main = runTests tests 
