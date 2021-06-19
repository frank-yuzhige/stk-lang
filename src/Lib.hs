{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Lib where

import Language.Stk
import qualified Prelude as P


[stk|

step/1 = 1 swap -;

fact/1 =
    1
    </1 = 1 eq/>
    (step)
    (*)
    primrec;

20 10 5 1 $[] (fact) map "world" : "hello" : print

|]
