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
    </1 = 1 eq/>
    (step)
    (*)
    primrec;

add/3 = $[] 0 (+) catarec;

mn = 4 5 6 $[] (fact) map ![] add print;

addMaybe/1 = 1 + 1 (eq) <! ;

|]

some = put (1 :: P.Int) |> (def @1 (args |> put (1 :: P.Int) |> eq))

main :: P.IO ()
main = stkMain mn
