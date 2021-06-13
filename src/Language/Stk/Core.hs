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
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Stk.Core where

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
type as :++: bs = HAppendListR as bs

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
app :: (Merge a s as, Merge b s bs) => Fn a b -> Fn as bs
app fn = eval . push fn

-- | Lift a haskell function to stk fn
lifn :: (a -> b) -> Fn '[a] '[b]
lifn f (a ::: _) = f a ::: HNil

-- | Lift a haskell function to stk fn (arity 2)
lifn2 :: (a -> b -> c) -> Fn '[a, b] '[c]
lifn2 f = eval . top lifn . eval . top lifn . push f

-- | Apply Haskell function to the top of the stack
top :: (a -> b) -> Stk (a : as) -> Stk (b : as)
top f (a ::: as) = f a ::: as

uncur = top lifn

a |> b = a >>> app b

{--- Functions ---}

-- | alias for push, in stk fn style
put :: a -> Fn0 a
put = push

-- | Duplicate the top value
dup :: Fn '[a] '[a, a]
dup (HCons a as) = HCons a (HCons a as)

add, sub, mul :: Num a => Fn '[a, a] '[a]
add = lifn2 (+)
sub = lifn2 (-)
mul = lifn2 (*)

ord :: Fn '[Char] '[Int]
ord = lifn fromEnum

chr :: Fn '[Int] '[Char]
chr = lifn toEnum

prog1 = runStk $ app (put 8 |> put 2 |> put 3 |> add |> mul |> chr |> put ')')


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