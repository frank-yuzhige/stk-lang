{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Lib
    ( main
    ) where

import Language.Stk
import qualified Prelude as P


[stk|

step/1 = 1 swap -;

fact/1 = 
    1 
    0 (eq) curry ! 
    (step) 
    (*) 
    primrec;

add/3 = $[] 0 (+) catarec;

mn = 4 5 6 $[] (fact) map ![] add print;

|]

main :: P.IO ()
main = stkMain mn
