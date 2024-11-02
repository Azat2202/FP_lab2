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
        ]

main : IO ()
main = runTests tests 
