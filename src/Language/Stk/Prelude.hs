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

import Prelude hiding ( const, div, mod, map, and, or, not, curry, uncurry )
import qualified Prelude

{--- Functions ---}

-- | Pop the top element from the stack
pop :: Fn '[a] '[]
pop = hTail

-- | Duplicate the top value
dup :: Fn '[a] '[a, a]
dup (HCons a as) = HCons a (HCons a as)

-- | Create a sub-stk on the current stk
new :: Fn '[] '[Stk '[]]
new = singleton

-- | Append the top element to the sub-stk
cons :: Fn '[a, Stk as] '[Stk (a : as)]
cons (a ::: stk ::: _) = singleton $ a ::: stk

-- | Dual of `cons`, extract the top element from the sub-stk to the current stk
uncons :: Fn '[Stk (a : as)] '[a, Stk as]
uncons ((a ::: stk) ::: _) = runStk $ put stk |> put a

-- | extract all elements from the sub-stk to the current stk
flat :: Fn '[Stk a] a
flat (stk ::: _) = stk

-- | Call the function at the top onto the remaining stack
class Call' as rs where
  call :: (LCheck as, LCheck rs) => Fn (Fn as rs : as) rs

type Call as rs = (Call' as rs, LCheck as, LCheck rs)

instance Call' '[] rs where
  call = eval

instance (Call' as rs) => Call' (a : as) rs where
  call = eval

-- | Function composition
compose :: Fn '[Fn a b, Fn b c] '[Fn a c]
compose (fab ::: fbc ::: _) = singleton (fab >>> fbc)

curry :: Fn '[Fn (a : as) r] '[Fn '[a] '[Fn as r]]
curry (fn ::: _) = singleton $ \(a ::: _) -> singleton $ \as -> fn (a ::: as)

uncurry :: forall a as r. (LCheck as, LCheck r)
         => Fn '[Fn '[a] '[Fn as r]] '[Fn (a : as) r]
uncurry (fn ::: _) = singleton $ \stk -> eval $ app fn stk

fflip :: forall a b c. LCheck c
      => Fn '[Fn '[a, b] c] '[Fn '[b, a] c]
fflip (fn ::: _) = singleton $ \(b ::: a ::: _) -> app fn (a ::: b ::: HNil)

-- | Swap 2 elements on top of the stack
swap :: Fn '[a, b] '[b, a]
swap (a ::: b ::: _) = b ::: a ::: HNil

-- | If statement
cond :: Fn '[Bool, a, a] '[a]
cond = lifn3 $ \b tr fl -> if b then tr else fl

add, sub, mul :: Num a => Fn '[a, a] '[a]
add = lifn2 (+)
sub = lifn2 (-)
mul = lifn2 (*)

div, mod, pow :: Integral a => Fn '[a, a] '[a]
div = lifn2 Prelude.div
mod = lifn2 Prelude.mod
pow = lifn2 (Prelude.^)

fpow :: Floating a => Fn '[a, a] '[a]
fpow = lifn2 (**)

eq, neq :: Eq a => Fn '[a, a] '[Bool]
eq = lifn2 (==)
neq = lifn2 (/=)

lt, gt, le, ge :: forall a. Ord a => Fn '[a, a] '[Bool]
lt = lifn2 (<)
gt = lifn2 (>)
le = lifn2 (<=)
ge = lifn2 (>=)

cmp :: Ord a => Fn '[a, a] '[Ordering]
cmp = lifn2 compare

ord :: Fn '[Char] '[Int]
ord = lifn fromEnum

chr :: Fn '[Int] '[Char]
chr = lifn toEnum

const :: Fn '[a, b] '[a]
const = lifn2 Prelude.const

and, or :: Fn '[Bool, Bool] '[Bool]
and = lifn2 (Prelude.&&)
or  = lifn2 (Prelude.||)

not :: Fn '[Bool] '[Bool]
not = lifn Prelude.not

class FListLengthEq (f :: * -> *) (n :: HNat) where
instance FListLengthEq Nil HZero
instance (FListLengthEq f n) => FListLengthEq (Cons f) (HSucc n)

type FHListSameLength f h n = (FixedList f, FListLengthEq f n, HLengthEq h n)

-- | Proof for the stack to be homogeneous
class (HLengthEq stk n) => HomoStk a n stk | stk -> n, a n -> stk where
  asList    :: Proxy n -> Stk stk -> [a]
  fromList' :: Proxy n -> [a] -> Stk stk  -- ^ partial

-- TODO: refactor using fixed-size list
instance HomoStk a HZero '[] where
  asList    _ _ = []
  fromList' _ _ = HNil

instance (HomoStk a n s) => HomoStk a (HSucc n) (a : s) where
  asList    _ (a ::: s) = a : asList (Proxy @n) s
  fromList' _ []        = error "Failed to construct a homogeneous stack due to insufficient elem in list"
  fromList' _ (a :   s) = a ::: fromList' (Proxy @n) s

map :: forall a b n as bs. (HomoStk a n as, HomoStk b n bs) => Fn '[Fn '[a] '[b], Stk as] '[Stk bs]
map (fn ::: as ::: _)
  = singleton
  . fromList' (Proxy @n)
  . Prelude.map (hHead . fn . singleton)
  . asList (Proxy @n)
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
      | otherwise = agg <| go <| next <| dup $ stk
      where
        (isStop ::: _) = stop stk

-- | catamorphism aka fold
catarec :: forall a b n as. (HomoStk a n as)
        => Fn '[Fn '[a, b] '[b]  -- aggregation function
               ,b                -- base value
               ,Stk as           -- stack
               ]
               '[b]              -- result
catarec (f ::: b ::: as ::: _)
  = singleton
  . Prelude.foldr f' b
  . asList (Proxy @n)
  $ as
  where
    f' k acc = get $ put acc |> put k |> f

-- TODO: implement me (non-deterministic generated stk size)
-- | anamorphism aka unfold
anarec :: forall a b n as. (HomoStk a n as)
       => Fn '[Fn '[b] '[Maybe (Stk '[a, b])]  -- generation function
              ,b                               -- base value
              ]
             '[Stk as]                         -- result
anarec (f ::: b ::: _) = undefined

factorial :: (Num a, Eq a) => Fn '[a] '[a]
factorial = get $
  put 1 |>
  put 1 |> put eq |> curry |> call |>
  put 1 |> put sub |> fflip |> curry |> call |>
  put mul |>
  put primrec |> curry |> call |> curry |> call |> curry |> call |> curry |> call


some = ((put (1)) |> put (1) |> put (eq) |> (curry) |> (call))
