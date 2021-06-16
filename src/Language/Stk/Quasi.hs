{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Language.Stk.Quasi (
  decl
) where

import Data.Void ( Void )
import Data.List ( intercalate )
import Data.Functor ( ($>), void )

import Text.Printf ( printf )

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
  four = 1 3 (+) call;

  three = 1 4 -;

  seven = three four +
|]

-}

data AST where
  PutInt  :: Int           -> AST
  PutChar :: Char          -> AST
  PutFn   :: Int -> String -> AST

put_ = "Language.Stk.Core.put"
instance Show AST where
  show (PutInt  i)  = printf "%s(%d)" put_ i
  show (PutChar c) = printf "%s(%s)"  put_ (show c)
  show (PutFn 0 f) = printf "(%s)" f
  show (PutFn n f) = printf "%s(%s)" put_ (show $ PutFn (n - 1) f)

type Parser e s m = (MonadParsec e s m, Token s ~ Char, Tokens s ~ String)

operator :: Parser e s m => m String
operator = some $ oneOf "!@#$%^&*:|+-/<>."

hardCodedOperator :: Parser e s m => m String
hardCodedOperator = choice [ string p $> s | (p, s) <- patterns] 
  where
    patterns = 
      [ ("[]", "_newStk"), (":", "_cons"), (".", "_compose"), ("if", "_if")
      , ("True", "_true"), ("False", "_false")
      ]

ident :: Parser e s m => m String
ident = (:) <$> letterChar <*> many (try (char '_') <|> try letterChar <|> digitChar)

symbol :: Parser e s m => m String
symbol = (try hardCodedOperator <|> try ident <|> operator) <* notFollowedBy digitChar

putInt :: Parser e s m => m AST
putInt = PutInt <$> L.signed space L.decimal

putFn :: Parser e s m => m AST
putFn = uncurry PutFn <$> parens symbol

parens :: Parser e s m => m a -> m (Int, a)
parens p = try unwrap <|> ((0, ) <$> p)
  where
    unwrap = do
      (n, r) <- between (char '(') (char ')') (parens p)
      return (n + 1, r)

parseStkAST :: Parser e s m => m [AST]
parseStkAST = space *> sepEndBy1 (try putFn <|> putInt) space1

astToStr :: [AST] -> String
astToStr = intercalate " Language.Stk.Core.|> " . map show

mapLeft :: Either t b -> (t -> a)  -> Either a b
mapLeft (Left  x) f = Left $ f x
mapLeft (Right y) _ = Right y

parseExpr :: String -> Either String Exp
parseExpr s = do
  ast <- parse @Void (parseStkAST <* eof) "" s `mapLeft` errorBundlePretty
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
