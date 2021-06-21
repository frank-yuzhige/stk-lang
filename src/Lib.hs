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

1 2 (+) !* print

|]
