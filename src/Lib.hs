{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}


module Lib
    ( someFunc
    ) where

import Language.Stk
import qualified Prelude as P


[stk|
nine = 3 2 1 * +;

step/1 = 1 swap -;

fact/1 = 
    1 
    1 (eq) curry ! 
    (step) 
    (*) 
    primrec;

fact10 = 10 fact;

pythX/2= dup * swap dup * + sqrt round;

pyth345 = 3 4 pythX;

results = pyth345 fact10;
|]

someFunc :: P.IO ()
someFunc = P.print (runStk results) 
