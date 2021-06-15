{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Language.Stk.Quasi (
  decl
) where

import Data.Void ( Void )
import Data.List ( intercalate )
import Data.Functor ( ($>), void )

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax
import Language.Haskell.Meta.Parse

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Language.Stk.Core as Stk


{-
stk language syntax:

[stk|>STK   # dependency qualified namespace

  # function definition
  four = 1 3 &+ call;

  three = 1 4 -;

  seven = three four +
|]

-}

data AST where
  PutInt  :: Int    -> AST
  PutFn   :: String -> AST
  CallFn  :: String -> AST

instance Show AST where
  show (PutInt i) = "Language.Stk.Core.put(" <> show i <> ")"
  show (PutFn  f) = "Language.Stk.Core.put(" <> f <> ")"
  show (CallFn f) = "(" <> f <> ")"

type Parser e s m = (MonadParsec e s m, Token s ~ Char, Tokens s ~ String)

operator :: Parser e s m => m String
operator = some symbolChar

ident :: Parser e s m => m String
ident = (:) <$> letterChar <*> many (try (char '_') <|> try letterChar <|> digitChar) 

putInt :: Parser e s m => m AST
putInt = PutInt <$> L.signed space L.decimal

putFn :: Parser e s m => m AST
putFn = PutFn <$> (char '&' *> (try ident <|> operator))

callFn :: Parser e s m => m AST
callFn = CallFn <$> (try ident <|> operator)

parseStkAST :: Parser e s m => m [AST]
parseStkAST = space *> sepEndBy1 (try putFn <|> try callFn <|> putInt) space1

astToStr :: [AST] -> String
astToStr = intercalate " Language.Stk.Core.|> " . map show 

mapLeft :: Either t b -> (t -> a)  -> Either a b
mapLeft (Left  x) f = Left $ f x
mapLeft (Right y) _ = Right y

parseExpr :: String -> Either String Exp
parseExpr s = do
  ast <- parse @Void parseStkAST "" s `mapLeft` errorBundlePretty
  let src = astToStr ast
  parseExp src `mapLeft` show

decl :: QuasiQuoter
decl = QuasiQuoter {
  quoteExp = \s -> do
    exp <- case parseExpr s of
      Left  err -> fail err
      Right e   -> return e
    [e| $(return exp) |]
}

-- stk :: QuasiQuoter
-- stk = QuasiQuoter {
--   quoteDec = \s -> do
    
-- }
