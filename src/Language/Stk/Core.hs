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
{-# LANGUAGE UndecidableInstances #-}

module Language.Stk.Core (
  module Language.Stk.Core,
  (>>>)
) where

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
type T t    = Fn '[] t

a |> b = a >>> app b
a <| b = b >>> app a

infixr 2 <|

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
put :: a -> Fn '[] '[a]
put = push

-- | Apply Haskell function to the top of the stack
top :: (a -> b) -> Stk (a : as) -> Stk (b : as)
top f (a ::: as) = f a ::: as

-- | Builds a new stack with a single object.
singleton :: a -> Stk '[a]
singleton a = a ::: HNil

class IsStk (a :: [*])
instance IsStk '[]
instance IsStk ts => IsStk (t : ts)

type SameLengthStk as bs = (IsStk as, IsStk bs, SameLength as bs)

type (:++:) :: [*] -> [*] -> [*]
type as :++: bs = HAppendListR as bs

-- | Find the base stack: [..front, ..base] = total
class Base' as bs ts | as ts -> bs, as bs -> ts where
  base  :: (as :++: bs ~ ts) => Proxy as -> Stk ts -> Stk bs

instance (ts ~ ts') => Base' '[] ts ts' where
  base Proxy n = n

instance (a ~ t, Base' as bs ts) => Base' (a : as) bs (t : ts) where
  base Proxy (_ ::: ts) = base (Proxy @as) ts

-- | Find the front stack: [..front, ..base] = total
class Front' as bs ts | as bs -> ts, as ts -> bs where
  front ::  (as :++: bs ~ ts) => Proxy bs -> Stk ts -> Stk as

instance (bs ~ ts) => Front' '[] bs ts where
  front _ _ = HNil

instance (Front' as bs ts, a ~ t) => Front' (a : as) bs (t : ts) where
  front _ (t ::: ts) = t ::: front (Proxy @bs) ts

type Append' a b ab = (HAppendList a b, HAppendListR a b ~ ab)

-- | Full proof for type-level lists that merges, that is, `as ++ bs == cs`
type Merge a b ab = (Base' a b ab, Front' a b ab, Append' a b ab)

-- | Trivial proofs on top of `Merge`, make GHC happy
type LCheck c = (c ~ HAppendListR c '[], Base' c '[] c, Front' c '[] c, HAppendList c '[], SameLength c c)

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

-- | Apply stk fn to tdue to he stack
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

lifn0 :: a -> Fn '[] '[a]
lifn0 = push

-- | Lift a haskell function to stk fn (arity 2)
lifn2 :: (a -> b -> c) -> Fn '[a, b] '[c]
lifn2 = lifnX (Proxy @2)

lifn3 :: (a -> b -> c -> d) -> Fn '[a, b, c] '[d]
lifn3 = lifnX (Proxy @3)

-- Unpack fn to haskell function
unpack :: (Stk '[a] -> Stk '[c]) -> a -> c
unpack fn = fromSingleton . fn . singleton


-- | Call the function at the top onto the remaining stack
class Call' as rs where
  call :: LChecks '[as, rs] => Fn (Fn as rs : as) rs
  call = eval

type Call as rs = (Call' as rs, LCheck as, LCheck rs)
instance Call' '[] rs
instance (Call' as rs) => Call' (a : as) rs


-- | Proof for the stack to be homogeneous

type HomStkR :: HNat -> * -> [*]
type family HomStkR n a = as where
  HomStkR HZero     a = '[]
  HomStkR (HSucc n) a = a : HomStkR n a

type HomStkLen :: * -> [*] -> HNat
type family HomStkLen a as = n where
  HomStkLen a '[] = HZero
  HomStkLen a (a : as) = HSucc (HomStkLen a as)

class (HomStkR (HomStkLen a as) a ~ as) => HomStk a as where
  asList    :: Stk as -> [a]
  fromList' :: [a] -> Stk (HomStkR (HomStkLen a as) a)  -- ^ partial

instance HomStk a '[] where
  asList    _ = []
  fromList' _ = HNil

instance (HomStk a as, a ~ a') => HomStk a' (a : as) where
  asList    (a ::: s) = a  :  asList s
  fromList' (a  :  s) = a ::: fromList' s
  fromList' []        = error "Failed to construct a homogeneous stack: Insufficient elem in list!"

-- | Non-empty homogeneous stack
type NonEmptyHomStk a as = (HomStk a as, HLengthGe as HZero)

-- | Fixed-size homogeneous stack
type FixedHomStk n a as = (HomStk a as, HomStkLen a as ~ n)

-- | Proof for 2 homogeneous stack to be of same length
class (HomStk a as, HomStk b bs, SameLength as bs) => SameLengthHomStk a as b bs | a as b -> bs, bs b a -> as
instance SameLengthHomStk a '[] b '[]
instance SameLengthHomStk a as b bs => SameLengthHomStk a (a : as) b (b : bs)

-- | Proof for the stack to be able to duplicate its top n elements
class (Merge a as aas, HTake n as a, HLengthEq a n, HLengthGe as n) => Dup n a as aas | n as -> aas a where
  dup' :: (HTake n as a, Merge a as aas) => Proxy n -> Fn as aas

instance Dup HZero '[] as as where
  dup' _ = id

instance (Dup n r rs rrs, Merge (a : r) (a : rs) arars) => Dup (HSucc n) (a : r) (a : rs) arars where
  dup' _ (a ::: rs) = merge (a ::: hTake (Proxy @n) rs) (a ::: rs)


class (SameLength as bs) => Rot (n :: HNat) as bs | n as -> bs where
  rot' :: Proxy n -> Fn as bs

instance (SameLength as as) => Rot HZero as as where
  rot' _ = id

instance (SameLength (a : s) sa, Merge s '[a] sa) => Rot (HSucc HZero) (a : s) sa where
  rot' _ (a ::: s) = merge s (singleton a)

instance (  Rot (HSucc n) (a : b : s) (b : s :++: '[a])
          , Merge s '[a, b] sab
          , SameLength (a : b : s) sab)
         => Rot (HSucc (HSucc n)) (a : b : s) sab where
  rot' _ (a ::: b ::: s) = hAppend s (a ::: b ::: HNil)
    where
      b ::: sa = rot' @(HSucc n) @(a : b : s) Proxy (a ::: b ::: s)

rotX :: forall n' as bs n. (Rot n as bs, Nat2HNat n' ~ n) => Proxy n' -> Fn as bs
rotX _ = rot' (Proxy @n)

dupX :: forall n' a as aas n. (Nat2HNat n' ~ n, Dup n a as aas)
     => Proxy n' -> Fn as aas
dupX _ = dup' (Proxy @n)

dupcall :: forall a s sa n aa. (Merge s a sa, Dup n a a aa)
        => Fn (Fn a s : a) sa
dupcall (fn ::: a) = runStk' a $ dup' (Proxy @n) |> fn

revdupcall :: forall a r ar ra aa nd nr. (Merge a r ar, Merge r a ra, Dup nd a a aa, Rot nr ra ar, HLengthEq r nr)
           => Fn (Fn a r : a) ar
revdupcall (fn ::: a) = runStk' a $ dup' (Proxy @nd) |> fn >>> rot' (Proxy @nr)

-- x = put 1 |> put 2 |> rot' (Proxy @(HSucc HZero))

-- | Definition of a combinator
--   Use case: def @(arity) (args |> function body)
def :: forall n' args ret n. (HLengthEq args n, HNat2Nat n ~ n', Nat2HNat n' ~ n)
    => Fn '[Stk args] ret -> Fn args ret
def a = runStk . (a .) . put

-- | extract all elements from the sub-stk to the current stk
args :: Fn '[Stk a] a
args (stk ::: _) = stk

-- | Specialized `hHead`
fromSingleton :: Stk '[a] -> a
fromSingleton = hHead

-- | get a value from a 0 arity `stk` fn.
get :: Fn '[] '[a] -> a
get = fromSingleton . runStk

stkIO :: Stk (IO a : ignore) -> IO ()
stkIO (io ::: _) = void io

stkMain :: Fn '[] (IO a : ignore) -> IO ()
stkMain = stkIO . runStk
