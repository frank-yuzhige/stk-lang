{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# OPTIONS_GHC -Wno-missing-fields #-}

module Language.Stk.Quasi (
  stk
) where

import Prelude hiding ( putChar, putStr )

import Data.Void ( Void )
import Data.Functor.Identity ( Identity )
import Data.List ( intercalate )
import Data.Functor ( ($>), void )

import Text.Printf ( printf )

import Language.Haskell.TH ( Exp, Dec )
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Parse
import Language.Haskell.Exts ( defaultParseMode, ParseMode(..), Extension(..), KnownExtension( DataKinds, TypeApplications, TypeFamilyDependencies, FlexibleContexts ) )

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


type HMetaParse n = String -> Either String n

data Elem where
  PutInt  :: Int           -> Elem
  PutChar :: Char          -> Elem
  PutStr  :: String        -> Elem
  PutFn   :: Int -> String -> Elem

newtype Elems = MkElems { unElems :: [Elem] }
instance Show Elems where
  show = intercalate _then . map show . unElems



instance Show Elem where
  show (PutInt  i) = printf "%s(%d :: P.Integer)" _put i
  show (PutChar c) = printf "%s(%s)"  _put (show c)
  show (PutStr  s) = printf "%s(%s)"  _put (show s)
  show (PutFn 0 f) = printf "(%s)" f
  show (PutFn n f) = printf "%s(%s)" _put (show $ PutFn (n - 1) f)

data Def = MkDef {
  defName :: String,
  arity   :: Int,
  defBody :: Elems
}
instance Show Def where
  show (MkDef name arity body) = printf "%s = %s @%d (%s |> %s)" name _def arity _args (show body)

type Parser e s m = (MonadParsec e s m, Token s ~ Char, Tokens s ~ String)

operator :: Parser e s m => m String
operator = some $ oneOf "!@#$%^&*:|+-/<>."

hardCodedOperator :: Parser e s m => m String
hardCodedOperator = choice [ string p $> s | (p, s) <- patterns]
  where
    patterns =
      [ ("[]", "_newStk"), ("::", "_swapcons"), (":", "_cons"), (".", "_compose"), ("if", "_if")
      , ("True", "_true"), ("False", "_false"), ("Nothing", "_nothing"), ("Just", "_just")
      , ("IO", "_io")
      ]

nat :: Parser e s m => m Int
nat = read <$> many digitChar

ident :: Parser e s m => m String
ident = (:) <$> letterChar <*> many (try (char '_') <|> try letterChar <|> digitChar)

symbol :: Parser e s m => m String
symbol = (try hardCodedOperator <|> try ident <|> operator) <* notFollowedBy digitChar

putInt :: Parser e s m => m Elem
putInt = PutInt <$> L.signed space L.decimal

putChar :: Parser e s m => m Elem
putChar = PutChar <$> between (char '\'') (char '\'') L.charLiteral

putStr :: Parser e s m => m Elem
putStr = PutStr <$> (char '"' *> manyTill L.charLiteral (char '"'))

putFn :: Parser e s m => m Elem
putFn = uncurry PutFn <$> parens symbol

parens :: Parser e s m => m a -> m (Int, a)
parens p = try unwrap <|> ((0, ) <$> p)
  where
    unwrap = do
      (n, r) <- between (char '(') (char ')') (parens p)
      return (n + 1, r)

parseStkElems :: Parser e s m => m Elems
parseStkElems = do
  space
  xs <- sepEndBy1 (try putInt <|> try putChar <|> try putStr <|> try putFn) space1
  return $ MkElems xs

parseDefArity :: Parser e s m => m Int
parseDefArity = try (char '/' *> space *> nat) <|> pure 0

parseStkDef :: Parser e s m => m Def
parseStkDef = do
  name  <- ident
  arity <- between space space parseDefArity
  char '='
  body <- parseStkElems
  char ';'
  return $ MkDef name arity body

parseStkDefs :: Parser e s m => m [Def]
parseStkDefs = space *> many (parseStkDef <* space)

mapLeft :: Either t b -> (t -> a)  -> Either a b
mapLeft (Left  x) f = Left $ f x
mapLeft (Right y) _ = Right y

qquoteExpr :: String -> Either String Exp
qquoteExpr = qquoteStk parseStkElems show parseExp

qquoteDef :: HMetaParse [Dec]
qquoteDef = qquoteStk 
  parseStkDefs 
  (unlines . map show) 
  (parseDecsWithMode defaultParseMode { extensions = EnableExtension <$> [
    DataKinds, TypeApplications, TypeFamilyDependencies, FlexibleContexts
  ]})

qquoteStk stkParse stkToMeta metaParse input = do
  stk <- parse @Void (stkParse <* eof) "" input `mapLeft` errorBundlePretty
  let src = stkToMeta stk
  metaParse src

stk :: QuasiQuoter
stk = QuasiQuoter {
  quoteExp =  \s -> do
    exp <- case qquoteExpr s of
      Left  err -> fail err
      Right e   -> return e
    [e| $(return exp) |],

  quoteType = error _stkErr,
  quotePat = error _stkErr,
  quoteDec = \s -> do
    case qquoteDef s of
      Left  err -> fail err
      Right e   -> return e
}

_stkErr = "Quasi-quotation 'stk' can only be used as top-level decs or exps"


_put, _def, _args, _then :: String
_put  = "Language.Stk.put"
_def  = "Language.Stk.def"
_args = "Language.Stk.args"
_then = " Language.Stk.|> "