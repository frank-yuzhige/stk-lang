module Main where

import qualified Lib ( main )

main :: IO ()
main = Lib.main


some :: a -> Maybe b -> Either a b
some a Nothing = Left a
some _ (Just b) = Right b

myFoldr :: (a -> b -> b) -> b -> [a] -> b
myFoldr _ b [] = b
myFoldr fabb b (a : as') = fabb a (myFoldr fabb b as')