{-# LANGUAGE QuasiQuotes #-}

module Language.Stk where

import Language.Stk.Quasi
import Language.Stk.Core
import Language.Stk.Prelude

import Prelude hiding (curry)

n = [decl| 1 2 -3 |]

f = [decl| 1 2 add 3 mul |]

fact = [decl| 
  10
  1 
  1  &eq  curry call 
  -1 &add curry call
  &mul
  primrec
|]

dupcallTest = [decl| 0 3 6 &add dupcall |]

composeTest = [decl| &swap &swap compose |]