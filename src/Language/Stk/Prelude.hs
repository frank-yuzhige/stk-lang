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
      Proxy(..) )
import Data.FixedList ( Cons((:.)), FixedList, Nil(..) )
import qualified Data.FixedList as F

import Prelude hiding ( const, div, mod, map, and, or, not, curry, uncurry, flip )
import qualified Prelude as P

{--- Functions ---}

-- | Pop the top element from the stack
pop :: Fn '[a] '[]
pop = hTail

-- | Duplicate the top value
dup :: Fn '[a] '[a, a]
dup = dupX (Proxy @1)

-- | Create a sub-stk on the current stk
_newStk :: Fn '[] '[Stk '[]]
_newStk = singleton

-- | Append the top element to the sub-stk
_cons :: Fn '[a, Stk as] '[Stk (a : as)]
_cons (a ::: stk ::: _) = singleton $ a ::: stk

-- | Dual of `cons`, extract the top element from the sub-stk to the current stk
uncons :: Fn '[Stk (a : as)] '[a, Stk as]
uncons ((a ::: stk) ::: _) = runStk $ put stk |> put a

-- | extract all elements from the sub-stk to the current stk
flat :: Fn '[Stk a] a
flat (stk ::: _) = stk

-- | Function composition
compose :: Fn '[Fn a b, Fn b c] '[Fn a c]
compose (fab ::: fbc ::: _) = singleton (fab >>> fbc)

curry :: Fn '[Fn (a : as) r] '[Fn '[a] '[Fn as r]]
curry (fn ::: _) = singleton $ \(a ::: _) -> singleton $ \as -> fn (a ::: as)

uncurry :: forall a as r. (LCheck as, LCheck r)
         => Fn '[Fn '[a] '[Fn as r]] '[Fn (a : as) r]
uncurry (fn ::: _) = singleton $ \stk -> eval $ app fn stk

flip :: forall a b c. LCheck c
      => Fn '[Fn '[a, b] c] '[Fn '[b, a] c]
flip (fn ::: _) = singleton $ \(b ::: a ::: _) -> app fn (a ::: b ::: HNil)

-- | Swap 2 elements on top of the stack
swap :: Fn '[a, b] '[b, a]
swap (a ::: b ::: _) = b ::: a ::: HNil

-- | If statement
cond :: Fn '[Bool, a, a] '[a]
cond = lifn3 $ \b tr fl -> if b then tr else fl

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
-- factorial :: (Num a, Eq a) => Fn '[a] '[a]
-- factorial = get $
--   put 1 |>
--   put 1 |> put eq |> curry |> call |>
--   put 1 |> put (-) |> fflip |> curry |> call |>
--   put mul |>
--   put primrec |> curry |> call |> curry |> call |> curry |> call |> curry |> call

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
      | otherwise = agg <| go <| next <| dup $ stk
      where
        (isStop ::: _) = stop stk

-- | catamorphism aka fold
catarec :: forall a b n as. (HomStk a n as)
        => Fn '[Fn '[a, b] '[b]  -- aggregation function
               ,b                -- base value
               ,Stk as           -- stack
               ]
               '[b]              -- result
catarec (f ::: b ::: as ::: _)
  = singleton
  . P.foldr f' b
  . asList (Proxy @n)
  $ as
  where
    f' k acc = get $ put acc |> put k |> f

-- TODO: implement me (non-deterministic generated stk size)
-- | anamorphism aka unfold
anarec :: forall a b n as. (HomStk a n as)
       => Fn '[Fn '[b] '[Maybe (Stk '[a, b])]  -- generation function
              ,b                               -- base value
              ]
             '[Stk as]                         -- result
anarec (f ::: b ::: _) = undefined

{- Operator symbols -}

(!) :: Call as rs => Fn (Fn as rs : as) rs
(!) = call


-- factorial :: (Num a, Eq a) => Fn '[a] '[a]
-- factorial = get $
--   put 1 |>
--   put 1 |> put eq |> curry |> call |>
--   put 1 |> put (-) |> fflip |> curry |> call |>
--   put mul |>
--   put primrec |> curry |> call |> curry |> call |> curry |> call |> curry |> call
