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

gen/1 = Nothing swap dup </1 = 1 + /> !* [] :: :: Just swap </1 = 10 gt/> ! if;


8 gen print

|]
