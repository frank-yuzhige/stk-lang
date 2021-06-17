{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Language.Stk.Prelude where

import Language.Stk.Core


import GHC.Types
import GHC.TypeNats
import Control.Arrow ((>>>))
import Data.HList
    ( hHead,
      hTail,
      HNat(..),
      HLengthEq,
      HList(HNil, HCons),
      Proxy(..), HNat2Nat, HTuple (hToTuple) )

import qualified Data.List  as P
import qualified Data.Maybe as P
import qualified Control.Monad as M

import Prelude hiding ( const, div, mod, map, and, or, not, curry, uncurry, flip )
import qualified Prelude as P

{--- Functions ---}

-- | Pop the top element from the stack
pop :: Fn '[a] '[]
pop = hTail

-- | Duplicate the top value
dup :: Fn '[a] '[a, a]
dup = dupX (Proxy @1)

-- | Swap 2 elements on top of the stack
swap :: Fn '[a, b] '[b, a]
swap (a ::: b ::: _) = b ::: a ::: HNil

-- | Duplicate the second element and bring it to the top
over :: Fn '[b, a] '[a, b, a]
over (b ::: a ::: _) = runStk $ put a |> put b |> put a

-- | Rotate the first 3 elements
rot :: Fn '[a, b, c] '[b, c, a]
rot (a ::: b ::: c ::: _) = runStk $ put a |> put c |> put b

-- | Create a sub-stk on the current stk
_newStk :: Fn '[] '[Stk '[]]
_newStk = singleton

-- | Append the top element to the sub-stk
_cons :: Fn '[a, Stk as] '[Stk (a : as)]
_cons (a ::: stk ::: _) = singleton $ a ::: stk

_swapcons :: Fn '[Stk as, a] '[Stk (a : as)]
_swapcons (stk ::: a ::: _) = singleton $ a ::: stk

-- | Dual of `cons`, extract the top element from the sub-stk to the current stk
uncons :: Fn '[Stk (a : as)] '[a, Stk as]
uncons ((a ::: stk) ::: _) = runStk $ put stk |> put a

-- | Push all elements in the current stack to a new sub-stack.
_packStk :: Fn a '[Stk a]
_packStk stk = stk ::: HNil

_unpackStk :: Fn '[Stk a] a
_unpackStk = hHead 

-- | Function composition
_compose :: Fn '[Fn a b, Fn b c] '[Fn a c]
_compose (fab ::: fbc ::: _) = singleton (fab >>> fbc)

curry :: Fn '[Fn (a : as) r] '[Fn '[a] '[Fn as r]]
curry (fn ::: _) = singleton $ \(a ::: _) -> singleton $ \as -> fn (a ::: as)

uncurry :: forall a as r. (LCheck as, LCheck r)
         => Fn '[Fn '[a] '[Fn as r]] '[Fn (a : as) r]
uncurry (fn ::: _) = singleton $ eval . app fn

flip :: forall a b c. LCheck c
      => Fn '[Fn '[a, b] c] '[Fn '[b, a] c]
flip (fn ::: _) = singleton $ \(b ::: a ::: _) -> app fn (a ::: b ::: HNil)

-- | If statement
_if :: Fn '[Bool, a, a] '[a]
_if = lifn3 $ \b tr fl -> if b then tr else fl

-- | Re-export True, False
_true, _false :: Fn '[] '[Bool]
_true  = put True
_false = put False

-- | Maths

(+), (-), (*) :: Num a => Fn '[a, a] '[a]
(+) = lifn2 (P.+)
(-) = lifn2 (P.-)
(*) = lifn2 (P.*)

(//), mod, pow :: Integral a => Fn '[a, a] '[a]
(//) = lifn2 P.div
mod = lifn2 P.mod
pow = lifn2 (P.^)

neg :: Num a => Fn '[a] '[a]
neg = lifn P.negate

(**) :: Floating a => Fn '[a, a] '[a]
(**) = lifn2 (P.**)

sqrt :: Floating a => Fn '[a] '[a]
sqrt = lifn P.sqrt

floor :: (RealFrac a, Integral b) => Fn '[a] '[b]
floor = lifn P.floor

round :: (RealFrac a, Integral b) => Fn '[a] '[b]
round = lifn P.round

castInt :: (Integral a, Num b) => Fn '[a] '[b]
castInt = lifn P.fromIntegral

eq, neq :: Eq a => Fn '[a, a] '[Bool]
eq  = lifn2 (P.==)
neq = lifn2 (P./=)

lt, gt, le, ge :: forall a. Ord a => Fn '[a, a] '[Bool]
lt = lifn2 (P.<)
gt = lifn2 (P.>)
le = lifn2 (P.<=)
ge = lifn2 (P.>=)

cmp :: Ord a => Fn '[a, a] '[Ordering]
cmp = lifn2 compare

ord :: Fn '[Char] '[Int]
ord = lifn fromEnum

chr :: Fn '[Int] '[Char]
chr = lifn toEnum

const :: Fn '[a, b] '[a]
const = lifn2 P.const

and, or :: Fn '[Bool, Bool] '[Bool]
and = lifn2 (P.&&)
or  = lifn2 (P.||)

not :: Fn '[Bool] '[Bool]
not = lifn P.not

{- Maybe combinators -}
_nothing :: Fn '[] '[Maybe a]
_nothing = put Nothing

_just :: Fn '[a] '[Maybe a]
_just = lifn Just

isNothing, isJust :: Fn '[Maybe a] '[Bool]
isNothing = lifn P.isNothing
isJust    = lifn P.isJust

fromMaybe :: Fn '[c, Maybe c] '[c]
fromMaybe = lifn2 P.fromMaybe

maybe :: Fn '[d, a -> d, Maybe a] '[d]
maybe = lifn3 P.maybe

{- Haskell Monad Combinators -}
_minject :: Monad m => Fn '[a] '[m a]
_minject = lifn P.return

-- reversed, since stack is reversed
(=<<) :: forall a b m. Monad m => Fn '[m a, Fn '[a] '[m b]] '[m b]
(=<<) (a ::: g ::: _) = lifn2 (P.>>=) (a ::: unpack g ::: HNil)

(<<) :: forall a b m. Monad m => Fn '[m a, m b] '[m b] 
(<<) (a ::: b ::: _) = lifn2 (M.>>) (a ::: b ::: HNil)

{- IO Combinators -}
_io :: Fn '[a] '[IO a]
_io = _minject

print :: Show a => Fn '[a] '[IO ()]
print = lifn P.print

putStr :: Fn '[String] '[IO ()]
putStr = lifn P.putStr

putStrLn :: Fn '[String] '[IO ()]
putStrLn = lifn P.putStrLn

{- Higher-order combinators -}

map :: forall a b as bs. SameLengthHomStk a as b bs
    => Fn '[Fn '[a] '[b], Stk as] '[Stk bs]
map (fn ::: as ::: _)
  = singleton
  . fromList'
  . P.map (hHead . fn . singleton)
  . asList
  $ as

{- Recursion combinators -}

-- | A more generalized version of joy's `primrec` combinator
primrec :: forall a. Fn
              '[Fn '[a, a] '[a]     -- aggregation function
               ,Fn '[a]    '[a]     -- recurse function
               ,Fn '[a]    '[Bool]  -- termination function
               ,a                   -- base value
               ,a                   -- start value
               ]
              '[a]                  -- result
primrec (agg ::: next ::: stop ::: b ::: s ::: _) = app go (s ::: HNil)
  where
    go :: Fn '[a] '[a]
    go stk@(curr ::: xs)
      | isStop    = singleton b
      | otherwise = runStk' stk $ dup |> next |> go |> agg
      where
        (isStop ::: _) = stop stk

-- | catamorphism aka fold
catarec :: forall a b as. (HomStk a as)
        => Fn '[Fn '[a, b] '[b]  -- aggregation function
               ,b                -- base value
               ,Stk as           -- stack
               ]
               '[b]              -- result
catarec (f ::: b ::: as ::: _)
  = singleton
  . P.foldr f' b
  . asList
  $ as
  where
    f' k acc = get $ put acc |> put k |> f

-- FIXME: implement me (non-deterministic generated stk size)
-- | anamorphism aka unfold
anarec :: forall a b as. (HomStk a as)
       => Fn '[Fn '[b] '[Maybe (Stk '[a, b])]  -- generation function
              ,b                               -- base value
              ]
             '[Stk as]                         -- result
anarec (f ::: base ::: _) = singleton . fromList' . P.unfoldr f'  $ base
  where
    f' :: b -> Maybe (a, b)
    f' b = hToTuple <$> get (put b |> f)

{- Operator symbols -}

(!) :: Call as rs => Fn (Fn as rs : as) rs
(!) = call

(~:) :: Fn '[Stk (a : as)] '[a, Stk as]
(~:) = uncons


-- c = put 'v' |> put 'a' |> n

-- c = def @'[Bool] (flat |> put 1 |> put 2 |> eq) 


-- factorial :: (Num a, Eq a) => Fn '[a] '[a]
-- factorial = get $
--   put 1 |>
--   put 1 |> put eq |> curry |> call |>
--   put 1 |> put (-) |> fflip |> curry |> call |>
--   put mul |>
--   put primrec |> curry |> call |> curry |> call |> curry |> call |> curry |> call
