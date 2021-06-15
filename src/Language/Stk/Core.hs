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
import Data.FixedList ( Cons((:.)), FixedList, Nil(..) )
import qualified Data.FixedList as F

import Prelude hiding ( const, div, mod, map, and, or, not, curry, uncurry )
import qualified Prelude

pattern (:::) :: x -> HList xs -> HList (x : xs)
pattern a ::: b = HCons a b
{-# COMPLETE (:::) :: HList #-}
infixr 2 :::

type Stk = HList

type Fn as bs = Stk as -> Stk bs
type Fn0 bs = Fn '[] '[bs]
type T t    = Fn '[] t

-- | Run the `stk` program on an empty execution stack 
runStk :: (Stk '[] -> b) -> b
runStk = runStk' HNil

-- | Run the `stk` program on a given execution stack
runStk' :: forall stk a. Stk stk -> (Stk stk -> a) -> a 
runStk' = flip ($)

-- | Push a value on to the stack
push :: a -> Stk as -> Stk (a : as)
push = HCons

-- | alias for push, in stk fn style
put :: a -> Fn0 a
put = push

type (:++:) :: [*] -> [*] -> [*]
type as :++: bs = (HAppendListR as bs)

-- | Find the base stack: [..front, ..base] = total
class Base' as bs ts | as ts -> bs where
  base  :: (as :++: bs ~ ts) => Proxy as -> Stk ts -> Stk bs

instance (ts ~ ts') => Base' '[] ts ts' where
  base Proxy n = n

instance (a ~ t, Base' as bs ts) => Base' (a : as) bs (t : ts) where
  base Proxy (_ ::: ts) = base (Proxy @as) ts

-- | Find the front stack: [..front, ..base] = total
class Front' as bs ts | as bs -> ts where
  front ::  (as :++: bs ~ ts) => Proxy bs -> Stk ts -> Stk as

instance (bs ~ ts) => Front' '[] bs ts where
  front _ _ = HNil

instance (Front' as bs ts, a ~ t) => Front' (a : as) bs (t : ts) where
  front _ (t ::: ts) = t ::: front (Proxy @bs) ts

type Append' a b ab = (HAppendList a b, HAppendListR a b ~ ab)

-- | Full proof for type-level lists that merges, that is, `as ++ bs == cs`
type Merge a b ab = (Base' a b ab, Front' a b ab, Append' a b ab)

-- | Trivial proofs on top of `Merge`, make GHC happy
type LCheck c = (c ~ HAppendListR c '[], Base' c '[] c, Front' c '[] c, HAppendList c '[])

type LChecks :: [[*]] -> Constraint
type family LChecks xs = c where
  LChecks '[] = ()
  LChecks (t : ts) = (LCheck t, LChecks ts)

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
rebase s = outbase s . inbase (Proxy @s)

-- | evaluate the stk stack as such:
--   [(fn a1 .. an -> b1 .. bn), a1, .., an, as] => [b1, .., bn, as]
eval :: forall a b s as bs. (Merge a s as, Merge b s bs) => Fn (Fn a b : as) bs
eval (fn ::: as) = rebase (base (Proxy @a) as) fn as

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
  stepX _ = stepX (Proxy @n) . eval . top lifn

type Nat2HNat :: Nat -> HNat
type family Nat2HNat n = c where
  Nat2HNat 0 = HZero
  Nat2HNat n = HSucc (Nat2HNat (n - 1))

-- | Lift a haskell function to `stk` fn. The number of 'steps' of such lift is determined
--   by the provided type that comes with `Proxy`.  
lifnX :: forall n n' a as. (Nat2HNat n' ~ n, StepX n a as)
      => Proxy n' -> a -> Stk as -> Stk (StepDownF n a : StepDownS n as)
lifnX n f = stepX (Proxy @n) . push f

lifn0 :: a -> Fn0 a
lifn0 = push

-- | Lift a haskell function to stk fn (arity 2)
lifn2 :: (a -> b -> c) -> Fn '[a, b] '[c]
lifn2 = lifnX (Proxy @2)

lifn3 :: (a -> b -> c -> d) -> Fn '[a, b, c] '[d]
lifn3 = lifnX (Proxy @3)

-- | Call the function at the top onto the remaining stack
class Call' as rs where
  call :: LChecks '[as, rs] => Fn (Fn as rs : as) rs
  call = eval

type Call as rs = (Call' as rs, LCheck as, LCheck rs)

instance Call' '[] rs

instance (Call' as rs) => Call' (a : as) rs


-- | Proof for the stack to be homogeneous
class (HLengthEq stk n) => HomStk a n stk | stk -> n, a n -> stk where
  asList    :: Proxy n -> Stk stk -> [a]
  fromList' :: Proxy n -> [a] -> Stk stk  -- ^ partial

-- TODO: refactor using fixed-size list
instance HomStk a (HSucc HZero) '[a] where
  asList    _ _ = []
  fromList' _   = (::: HNil) . head

instance (HomStk a n s) => HomStk a (HSucc n) (a : s) where
  asList    _ (a ::: s) = a  :  asList    (Proxy @n) s
  fromList' _ (a  :  s) = a ::: fromList' (Proxy @n) s
  fromList' _ []        = error "Failed to construct a homogeneous stack due to insufficient elem in list"

-- | Proof for the stack to be able to duplicate its top n elements
class (Front' a as aas) => Dup' n a as aas | n as -> aas a where
  dup' :: (HTake n as a, Merge a as aas) => Proxy n -> Fn as aas

type Dup n a as aas = (Dup' n a as aas, Merge a as aas, HTake n as a, HLengthEq a n, HLengthGe as n)

instance Dup' HZero '[] as as where
  dup' _ = id

instance (Dup n r rs rrs, Merge (a : r) (a : rs) arars) => Dup' (HSucc n) (a : r) (a : rs) arars where
  dup' _ (a ::: rs) = merge (a ::: r) (a ::: rs)
    where 
      r = hTake (Proxy @n) rs

dupX :: forall n' a as aas n. (Nat2HNat n' ~ n, Dup n a as aas) 
     => Proxy n' -> Fn as aas
dupX _ = dup' (Proxy @n)

dupcall :: forall a s sa n aa. (LChecks '[a, s, sa, aa], Merge a a aa, Merge s a sa, Dup n a a aa) 
        => Fn (Fn a s : a) sa
dupcall (fn ::: a) = runStk' a $ dup' (Proxy @n) |> fn

-- | Apply Haskell function to the top of the stack
top :: (a -> b) -> Stk (a : as) -> Stk (b : as)
top f (a ::: as) = f a ::: as

-- | Builds a new stack with a single object.
singleton :: a -> Stk '[a]
singleton a = a ::: HNil

-- | Specialized `hHead`
fromSingleton :: Stk '[a] -> a
fromSingleton = hHead

-- | get a value from a 0 arity `stk` fn.
get :: Fn '[] '[a] -> a
get f = fromSingleton $ app f HNil

a |> b = a >>> app b
a <| b = b >>> app a

infixr 2 <|
