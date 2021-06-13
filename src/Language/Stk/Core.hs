{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Stk.Core where

import GHC.Types
import GHC.TypeNats
import Control.Arrow ((>>>))
import Data.HList

import Prelude hiding ( const, div, mod )
import qualified Prelude

{-

1. Literals: (e.g. 1, 2, .., [], [1, 2], .. ) :: fn [] -> [typeof Literal]
2. Functions: (e.g. +, -, map) :: fn [arg1, arg2, ..] -> [ret1, ret2, ...]
3. Keywords:
  3.1: @app 

-}

pattern (:::) :: x -> HList xs -> HList (x : xs)
pattern a ::: b = HCons a b
infixr 2 :::

type Stk = HList

type Fn as bs = Stk as -> Stk bs
type Fn0 bs = Fn '[] '[bs]

-- | Run the `stk` program on an empty execution stack 
runStk :: (Stk '[] -> b) -> b
runStk = ($ HNil)

-- | Push a value on to the stack
push :: a -> Stk as -> Stk (a : as)
push = HCons

type (:++:) :: [*] -> [*] -> [*]
type as :++: bs = (HAppendListR as bs)

-- | Find the base stack: [..front, ..base] = total
class Base' as bs ts | as ts -> bs where
  base  :: (as :++: bs ~ ts) => Proxy as -> Stk ts -> Stk bs

instance (ts ~ ts') => Base' '[] ts ts' where
  base Proxy n = n

instance (a ~ t, Base' as bs ts) => Base' (a : as) bs (t : ts) where
  base Proxy (_ ::: ts) = base (Proxy :: Proxy as) ts

-- | Find the front stack: [..front, ..base] = total
class Front' as bs ts | as bs -> ts where
  front ::  (as :++: bs ~ ts) => Proxy bs -> Stk ts -> Stk as

instance (bs ~ ts) => Front' '[] bs ts where
  front _ _ = HNil

instance (Front' as bs ts, a ~ t) => Front' (a : as) bs (t : ts) where
  front _ (t ::: ts) = t ::: front (Proxy :: Proxy bs) ts

type Append' a b ab = (HAppendList a b, HAppendListR a b ~ ab)

-- | Full proof for type-level lists that merges, that is, `as ++ bs == cs`
type Merge a b ab = (Base' a b ab, Front' a b ab, Append' a b ab)

-- | Trivial proofs on top of `Merge`, make GHC happy
type LCheck c = (c ~ HAppendListR c '[], Base' c '[] c, Front' c '[] c, HAppendList c '[])

-- | `Data.HList.hAppend` with `Merge` proof present
merge :: forall a b ab. (Merge a b ab) => Stk a -> Stk b -> Stk ab
merge = hAppend

-- | Lift (fn a -> b) to (fn [..a, ..s] -> b).
--   `Proxy` as we do not care about what is in s
inbase :: forall a b s as. (Merge a s as) => Proxy s -> Fn a b -> Fn as b
inbase pr fn = fn . front pr

-- | Lift (fn a -> b) to (fn a -> [..b, ..s]), with the provided base stack `s`
outbase :: forall a b s bs. (Merge b s bs) => Stk s -> Fn a b -> Fn a bs
outbase s fn = flip merge s . fn

-- | Rebase a `stk` function (fn a -> b) to (fn [..a, ..s] -> [..b, ..s]), with the provided base stack `s` 
rebase :: forall a b s as bs. (Merge a s as, Merge b s bs) => Stk s -> Fn a b -> Fn as bs
rebase s = outbase s . inbase (Proxy :: Proxy s)

-- | evaluate the stk stack as such:
--   [(fn a1 .. an -> b1 .. bn), a1, .., an, as] => [b1, .., bn, as]
eval :: forall a b s as bs. (Merge a s as, Merge b s bs) => Fn (Fn a b : as) bs
eval (fn ::: as) = rebase (base (Proxy :: Proxy a) as) fn as

-- | Apply stk fn to the stack
app :: forall a b s as bs. (Merge a s as, Merge b s bs) => Fn a b -> Fn as bs
app fn = eval . push fn

-- | Lift a haskell function to stk fn
lifn :: (a -> b) -> Fn '[a] '[b]
lifn f (a ::: _) = f a ::: HNil

-- | Take n steps down with a haskell type
type family StepDownF n f where
  StepDownF HZero f = f
  StepDownF (HSucc n) (a -> b) = StepDownF n b

-- | Take n steps down with a `stk` fn type
type family StepDownS n s where
  StepDownS HZero f = f
  StepDownS (HSucc n) (a : b) = StepDownS n b

-- | Find the corresponding haskell-type-to-stk-type relation after `n` 'steps' down from the original type.
class StepX n f s where
  stepX :: (Merge '[f] s fs) => Proxy n -> Stk fs -> Stk (StepDownF n f : StepDownS n s)

instance StepX HZero f s where
  stepX _ = id

instance (StepX n f s) => StepX (HSucc n) (a -> f) (a : s) where
  stepX _ = stepX (Proxy :: Proxy n) . eval . top lifn

type Nat2HNat :: Nat -> HNat
type family Nat2HNat n = c where
  Nat2HNat 0 = HZero
  Nat2HNat n = HSucc (Nat2HNat (n - 1))

-- | Lift a haskell function to `stk` fn. The number of 'steps' of such lift is determined
--   by the provided type that comes with `Proxy`.  
lifnX :: forall n n' a as. (Nat2HNat n' ~ n, StepX n a as)
      => Proxy n' -> a -> Stk as -> Stk (StepDownF n a : StepDownS n as)
lifnX n f = stepX (Proxy :: Proxy n) . push f

lifn0 :: a -> Fn0 a
lifn0 = push

-- | Lift a haskell function to stk fn (arity 2)
lifn2 :: (a -> b -> c) -> Fn '[a, b] '[c]
lifn2 = lifnX (Proxy :: Proxy 2)

lifn3 :: (a -> b -> c -> d) -> Fn '[a, b, c] '[d]
lifn3 = lifnX (Proxy :: Proxy 3)

-- | Apply Haskell function to the top of the stack
top :: (a -> b) -> Stk (a : as) -> Stk (b : as)
top f (a ::: as) = f a ::: as

-- | Builds a new stack with a single object.
singleton :: a -> Stk '[a]
singleton a = a ::: HNil

-- | Alias for `singleton`, specialized to `stk` fn type.
def :: Fn a b -> Stk '[Fn a b]
def = singleton

a |> b = a >>> app b
a <| b = b >>> app a

infixr 2 <|

{--- Functions ---}

-- | alias for push, in stk fn style
put :: a -> Fn0 a
put = push

-- | Pop the top element from the stack
pop :: Fn '[a] '[]
pop = hTail

-- | Duplicate the top value
dup :: Fn '[a] '[a, a]
dup (HCons a as) = HCons a (HCons a as)

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
compose (fab ::: fbc ::: _) = def (fab >>> fbc)

fcurry :: Fn '[Fn (a : as) r] '[Fn '[a] '[Fn as r]]
fcurry (fn ::: _) = def $ \(a ::: _) -> def $ \as -> fn (a ::: as)

funcurry :: forall a as r. (LCheck as, LCheck r)
         => Fn '[Fn '[a] '[Fn as r]] '[Fn (a : as) r]
funcurry (fn ::: _) = def $ \stk -> eval $ app fn stk

fflip :: forall a b c. LCheck c
      => Fn '[Fn '[a, b] c] '[Fn '[b, a] c]
fflip (fn ::: _) = def $ \(b ::: a ::: _) -> app fn (a ::: b ::: HNil)

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

{- Recursion combinators -}
-- | A more generalized version of `joy`'s `primrec` combinator
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

prog1 = runStk . app $ (
  cond <| eq <| put EQ <| cmp <| put 'a' <| put 'b' <| put "a == b" <| put "a != b"
  )


factorial :: Integer -> Stk '[Integer]
factorial x = runStk . app $
  put x |>
  put 1 |>
  put 1 |> put eq |> fcurry |> call |>
  put 1 |> put sub |> fflip |> fcurry |> call |>
  put mul |>
  primrec @Integer
