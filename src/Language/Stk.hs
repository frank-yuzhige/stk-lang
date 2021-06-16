{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

module Language.Stk where

import Language.Stk.Quasi
import Language.Stk.Core
import Language.Stk.Prelude

import qualified Prelude as P


n = [decl| 1 2 -3 |]

f = [decl| 1 2 + 3 * |]

fact = [decl| 
  10
  1 
  1  (eq) curry ! 
  -1 (+) curry !
  (*)
  primrec
|]

dupcallTest = [decl| 0 3 6 ((+)) call dupcall |]

newTest = [decl| [] 1 : 2 : 3 :|]

composeTest = [decl| (swap) (swap) . |]

ifTest = [decl| 1 0 3 5 eq if |]