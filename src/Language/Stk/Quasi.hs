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

import Prelude hiding ( stkChar, stkStr )

import Control.Monad.State.Strict

import Data.Void ( Void )
import Data.Functor.Identity ( Identity )
import Data.List ( intercalate, (\\) )
import Data.Maybe ( fromJust, fromMaybe )
import Data.Functor ( ($>), void )
import Data.Map ( Map )

import Text.Printf ( printf )

import Language.Haskell.TH ( Exp, Dec )
import Language.Haskell.TH.Quote
import Language.Haskell.Meta.Parse
import Language.Haskell.Exts ( defaultParseMode, ParseMode(..), Extension(..), KnownExtension( DataKinds, TypeApplications, TypeFamilyDependencies, FlexibleContexts ) )

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Data.Map                   as M
import qualified Language.Stk.Core          as Stk
import qualified Control.Monad

type HMetaParse n = String -> Either String n

data Elem where
  EInt    :: Int             -> Elem
  EChar   :: Char            -> Elem
  EStr    :: String          -> Elem
  ESymbol :: String          -> Elem
  Put     :: Elem            -> Elem
  Direct  :: String          -> Elem
  Lambda  :: Arity -> [Elem] -> Elem
  StkLit  :: [Elem]          -> Elem

newtype Elems = MkElems { unElems :: [Elem] }

joinOp :: Elem -> String
joinOp (Direct _) = _arr
joinOp _          = _then

instance Show Elems where
  show = joinShow . unElems
    where
      joinShow []  = ""
      joinShow [x] = show x
      joinShow (x : y : xs) = show x <> joinOp y <> joinShow (y : xs)

instance Show Elem where
  show (EInt  i)     = printf "(%d :: P.Integer)" i
  show (EChar c)     = printf "(%s)" (show c)
  show (EStr  s)     = printf "(%s)" (show s)
  show (ESymbol s)   = printf "(%s)" s
  show (Direct  d)   = d
  show (Put     e)   = printf "%s(%s)" _put (show e)
  show (Lambda a bs) = printf "(%s @%d %s)" _def a (show $ MkElems (ESymbol _args : bs))
  show (StkLit es)   = show $ MkElems (ESymbol _newStk : concat [[e, ESymbol _cons] | e <- es])

type Arity = Int

data Def = MkDef {
  defName :: String,
  arity   :: Arity,
  defBody :: [Elem]
}

instance Show Def where
  show (MkDef name arity body) = printf "%s = %s @%d (%s)" name _def arity (show $ MkElems (ESymbol _args : body))

type Parser e s m = (MonadParsec e String m, MonadFail m)

-- | operators: 1. not start with '$' (direct put), or '#' (macro)
operator :: Parser e s m => m String
operator = try $ do
  x <- (:) <$> oneOf validOperatorStartChars <*> many (oneOf validOperatorChars)
  forM_ reservedOps $ \(op, cause) ->
    when (x == op) $ fail cause
  return x
  where
    validOperatorChars = "!@#$%^&*:|+-/\\<>.~?"
    validOperatorStartChars = validOperatorChars \\ "$#"
    reservedOps = [("/>", "end-of-lambda")]

hardCodedOperator :: Parser e s m => m String
hardCodedOperator = choice [ string p $> s | (p, s) <- patterns]
  where
    patterns =
      [ ("[]", "_newStk"), ("::", "_swapcons"), (":", "_cons"), (".", "_compose"), ("if", "_if")
      , ("![]", _unpack)
      , ("True", "_true"), ("False", "_false"), ("Nothing", "_nothing"), ("Just", "_just")
      , ("IO", "_io")
      ]

nat :: Parser e s m => m Int
nat = read <$> many digitChar

ident :: Parser e s m => m String
ident = (:) <$> letterChar <*> many (try (char '_') <|> try letterChar <|> digitChar)

symbol :: Parser e s m => m String
symbol = (try hardCodedOperator <|> try ident <|> operator) <* notFollowedBy digitChar

stkInt :: Parser e s m => m Elem
stkInt = Put . EInt <$> L.signed space L.decimal

stkChar :: Parser e s m => m Elem
stkChar = Put . EChar <$> between (char '\'') (char '\'') L.charLiteral

stkStr :: Parser e s m => m Elem
stkStr = Put . EStr <$> (char '"' *> manyTill L.charLiteral (char '"'))

stkSymbol :: Parser e s m => m Elem
stkSymbol = ESymbol <$> symbol

stkElem :: Parser e s m => m Elem
stkElem = do
  (puts, elem) <- parens (try lambda <|> try stkInt <|> try stkChar <|> try stkStr <|> stkSymbol)
  return $ foldr ($) elem [Put | _ <- [1..puts]]

direct :: Parser e s m => m Elem
direct = Direct <$> (char '$' *> choice [ string p $> s | (p, s) <- patterns])
  where
    patterns = [("[]", _pack)]

lambda :: Parser e s m => m Elem
lambda = do
  string "</"
  arity <- try (nat <* space <* char '=') <|> pure 0
  space
  body <- parseStkElems
  string "/>"
  return . Put $ Lambda arity body

parens :: Parser e s m => m a -> m (Int, a)
parens p = try unwrap <|> ((0,) <$> p)
  where
    unwrap = do
      (n, r) <- between (char '(') (char ')') (parens p)
      return (n + 1, r)

parseStkElems :: Parser e s m => m [Elem]
parseStkElems = sepEndBy1 (try direct <|> stkElem) space1

parseDefArity :: Parser e s m => m Int
parseDefArity = try (char '/' *> space *> nat) <|> pure 0

parseStkDef :: Parser e s m => m Def
parseStkDef = do
  name  <- ident
  arity <- between space space parseDefArity
  char '='
  space
  body <- parseStkElems
  char ';'
  return $ MkDef name arity body

parseStkDefs :: Parser e s m => m [Def]
parseStkDefs = space *> many (parseStkDef <* space)

parseStkModule :: Parser e s m => m ([Def], [Elem])
parseStkModule = do
  normalFns <- parseStkDefs
  mainBody  <- try parseStkElems <|> pure []
  try (char ';' *> space) <|> pure ()
  return (normalFns, mainBody)

writeModule :: ([Def], [Elem]) -> String
writeModule (defs, mainBody)
  | null mainBody = unlines (map show defs)
  | otherwise     = unlines (_mainDecl ++ [show (MkDef "_main" 0 mainBody)] ++ map show defs)
  where
    _mainDecl = ["main = stkMain _main"]

mapLeft :: Either t b -> (t -> a)  -> Either a b
mapLeft (Left  x) f = Left $ f x
mapLeft (Right y) _ = Right y

qquoteExpr :: String -> Either String Exp
qquoteExpr = qquoteStk parseStkElems show parseExp

qquoteDef :: HMetaParse [Dec]
qquoteDef = qquoteStk
  parseStkModule
  writeModule
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


_put, _def, _args, _pack, _unpack, _then, _arr :: String
_newStk, _cons :: String
_put  = "Language.Stk.put"
_def  = "Language.Stk.def"
_args = "Language.Stk.args"
_pack = "Language.Stk._packStk"
_unpack = "Language.Stk._unpackStk"
_then = " Language.Stk.|> "
_arr  = " Language.Stk.>>> "
_newStk = "Language.Stk._newStk"
_cons = "Language.Stk._cons"
