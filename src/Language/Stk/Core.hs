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
import Data.HList.FakePrelude

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

runStk :: (Stk '[] -> b) -> b
runStk = ($ HNil)

-- | Push a value on to the stack
push :: a -> Stk as -> Stk (a : as)
push = HCons

-- | Pop the top value off the stack
pop :: Stk (a : as) -> Stk as
pop = hTail

type (:++:) :: [*] -> [*] -> [*]
type as :++: bs = (HAppendListR as bs)

class Base' as bs ts | as ts -> bs where
  base  :: (as :++: bs ~ ts) => Proxy as -> Stk ts -> Stk bs

instance (ts ~ ts') => Base' '[] ts ts' where
  base Proxy n = n

instance (a ~ t, Base' as bs ts) => Base' (a : as) bs (t : ts) where
  base Proxy (_ ::: ts) = base (Proxy :: Proxy as) ts

class Front' as bs ts | as bs -> ts where
  front ::  (as :++: bs ~ ts) => Stk bs -> Stk ts -> Stk as

instance (bs ~ ts) => Front' '[] bs ts where
  front _ _ = HNil 

instance (Front' as bs ts, a ~ t) => Front' (a : as) bs (t : ts) where
  front bs (t ::: ts) = t ::: front bs ts

type Merge a b ab = (Base' a b ab, Front' a b ab, HAppendList a b, a :++: b ~ ab)

merge :: forall a b ab. (Merge a b ab) => Stk a -> Stk b -> Stk ab
merge = hAppend 

inbase :: forall a b s as. (Merge a s as) => Stk s -> Fn a b -> Fn as b
inbase s fn = fn . front s

outbase :: forall a b s bs. (Merge b s bs) => Stk s -> Fn a b -> Fn a bs
outbase s fn = flip merge s . fn

rebase :: forall a b s as bs. (Merge a s as, Merge b s bs) => Stk s -> Fn a b -> Fn as bs
rebase s = outbase s . inbase s

tobase :: forall a b s as. (Merge a s as) => Fn a b -> Stk as -> Stk s
tobase fn = base (Proxy :: Proxy a)

-- | evaluate the stk stack as such:
--   [(fn a1 .. an -> b1 .. bn), a1, .., an, as] => [b1, .., bn, as]
eval :: forall a b s as bs. (Merge a s as, Merge b s bs) => Stk (Fn a b : as) -> Stk bs
eval (fn ::: as) = rebase (tobase fn as) fn as

-- | Apply stk fn to the stack
app :: forall a b s as bs. (Merge a s as, Merge b s bs) => Fn a b -> Fn as bs
app fn = eval . push fn


-- | Lift a haskell function to stk fn
lifn :: (a -> b) -> Fn '[a] '[b]
lifn f (a ::: _) = f a ::: HNil

type family StepDownF n f where
  StepDownF HZero f = f
  StepDownF (HSucc n) (a -> b) = StepDownF n b

type family StepDownS n s where
  StepDownS HZero f = f
  StepDownS (HSucc n) (a : b) = StepDownS n b

class StepX n f s where
  stepX :: (Merge '[f] s fs) => Proxy n -> Stk fs -> Stk (StepDownF n f : StepDownS n s)

instance StepX HZero f s where
  stepX _ = id

type Nat2HNat :: Nat -> HNat
type family Nat2HNat n = c where
  Nat2HNat 0 = HZero
  Nat2HNat n = HSucc (Nat2HNat (n - 1))

instance (StepX n f s) => StepX (HSucc n) (a -> f) (a : s) where
  stepX _ = stepX (Proxy :: Proxy n) . eval . top lifn

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

uncur = top lifn

a |> b = a >>> app b
a <| b = b >>> app a

infixr 2 <|
{--- Functions ---}

-- | alias for push, in stk fn style
put :: a -> Fn0 a
put = push

singleton :: a -> Stk '[a]
singleton = runStk . push 

def :: Fn a b -> Stk '[Fn a b]
def = singleton

-- | Duplicate the top value
dup :: Fn '[a] '[a, a]
dup (HCons a as) = HCons a (HCons a as)

compose :: Fn '[Fn a b, Fn b c] '[Fn a c]
compose (fab ::: fbc ::: _) = def (fab >>> fbc)

fcurry :: Fn '[Fn (a : as) r] '[Fn '[a] '[Fn as r]]
fcurry (fn ::: _) = def $ \(a ::: _) -> def $ \as -> fn (a ::: as)

-- TODO: Implement me (Couldn't match type ‘c’ with ‘HAppendListR c '[]’)
-- fflip :: forall a b c. Fn '[Fn '[a, b] c] '[Fn '[b, a] c]
-- fflip (fn ::: _) = def $ \(b ::: a ::: _) -> app fn (a ::: b ::: HNil)

-- TODO: Implement me
-- funcurry :: forall a as r. Fn '[Fn '[a] '[Fn as r]] '[Fn (a : as) r]
-- funcurry (fn ::: _) = def $ \stk -> (eval @as @r @'[] @as @r) $ app fn stk

add, sub, mul :: Num a => Fn '[a, a] '[a]
add = lifn2 (+)
sub = lifn2 (-)
mul = lifn2 (*)

eq :: forall a. Eq a => Fn '[a, a] '[Bool]
eq = lifn2 (==)

lt :: forall a. Ord a => Fn '[a, a] '[Bool]
lt = lifn2 (<)

neq :: Eq a => Fn '[a, a] '[Bool]
neq = lifn2 (/=)

cmp :: Ord a => Fn '[a, a] '[Ordering]
cmp = lifn2 compare

ord :: Fn '[Char] '[Int]
ord = lifn fromEnum

chr :: Fn '[Int] '[Char]
chr = lifn toEnum

cond :: Fn '[Bool, a, a] '[a]
cond = lifn3 $ \b tr fl -> if b then tr else fl

flp :: Fn '[a, b] '[b, a]
flp (a ::: b ::: _) = b ::: a ::: HNil

{- Recursion combinators -}


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


factorial x = runStk . app $
  put x |> 
  put 1 |> 
  put 1 |> put eq |> fcurry >>> eval |> 
  put (-1) |> put add |> fcurry >>> eval |> 
  put mul |> 
  primrec @Integer
  -- (primrec @Integer) <| put mul <| fcurry <| put sub <| put 1 <| fcurry <| put (eq @Integer) <| put 0 <| put 1 <| put 10 




-- flp :: (a : b : xs) :->: (b : a : xs)
-- flp (HCons a (HCons b xs)) = HCons b (HCons a xs)

-- cond :: (b : b : (a -> Bool) : a : xs) :->: (b : xs)
-- cond (HCons fl (HCons tr (HCons p (HCons a xs)))) = HCons r xs
--   where r = if p a then tr else fl

-- primrec :: forall a as.
--            ((a -> a -> a)  -- fold function
--          : (a -> a)        -- 
--          : (a -> Bool)     -- termination predicate function
--          : a               -- base value
--          : a               -- starting value
--          : as) 
--          :->: (a : as)
-- primrec (HCons r (HCons cont (HCons p (HCons b xs)))) = go xs
--   where
--     go :: forall xs. (a : xs) :->: (a : xs)
--     go stk@(HCons n xs)
--       | p n       = push b xs
--       | otherwise = lapp (r (cont n)) stk

-- fib x =   push x 
--       >>> push 1 
--       >>> push 1
--       >>> 