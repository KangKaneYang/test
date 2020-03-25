-- https://www.codewars.com/kata/5c302f562f6fe300155a1933/train/haskell
{-# LANGUAGE TypeOperators, TypeFamilies, GADTs,
  UndecidableInstances #-}

module Kata.TimesComm where

import Kata.TimesComm.Definitions

{- Preloaded code. Maybe helpful for local editing.

-- | The natural numbers, encoded in types.
data Z
data S n

-- | Predicate describing natural numbers.
-- | This allows us to reason with `Nat`s.
data Natural :: * -> * where
  NumZ :: Natural Z
  NumS :: Natural n -> Natural (S n)

-- | Predicate describing equality of natural numbers.
data Equal :: * -> * -> * where
  EqlZ :: Equal Z Z
  EqlS :: Equal n m -> Equal (S n) (S m)

-- | Peano definition of addition.
type family (:+:) (n :: *) (m :: *) :: *
type instance Z :+: m = m
type instance S n :+: m = S (n :+: m)

-- | Peano definition of multiplication.
type family (:*:) (n :: *) (m :: *) :: *
type instance Z :*: m = Z
type instance S n :*: m = m :+: (n :*: m)

-}
-- This will be helpful
plus' :: Equal n m -> Natural a -> Equal (n :+: a) (m :+: a)
plus' EqlZ NumZ = EqlZ
plus' (EqlS eq) NumZ = EqlS $ plus' eq NumZ
plus' EqlZ (NumS n) = EqlS $ plus' EqlZ n

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-plus-c-equals-a-plus-b-plus-c-prove-it/haskell
reflexive :: Natural n -> Equal n n
reflexive NumZ = EqlZ
reflexive (NumS n) = EqlS $ reflexive n

-- | if a = b, then b = a.
symmetric :: Equal a b -> Equal b a
symmetric EqlZ = EqlZ
symmetric (EqlS e) = EqlS $ symmetric e

-- This is the proof that the kata requires.
-- | a + (b + c) = (a + b) + c
plusAssoc ::
     Natural a
  -> Natural b
  -> Natural c
  -> Equal (a :+: (b :+: c)) ((a :+: b) :+: c)
plusAssoc NumZ NumZ NumZ = EqlZ
-- plusAssoc NumZ (NumS b) NumZ = EqlS $ plusAssoc NumZ b NumZ
plusAssoc NumZ NumZ (NumS c) = EqlS $ plusAssoc NumZ NumZ c
plusAssoc NumZ (NumS b) c = EqlS $ plusAssoc NumZ b c
plusAssoc (NumS a) b c = EqlS $ plusAssoc a b c

-- | You need this! Copy your solution from
-- https://www.codewars.com/kata/a-plus-b-equals-b-plus-a-prove-it/haskell
subst :: Equal a b -> Equal b c -> Equal a c
subst EqlZ EqlZ = EqlZ
subst (EqlS a) (EqlS b) = EqlS $ subst a b

plusS :: Natural a -> Natural b -> Equal (S a :+: b) (a :+: S b)
plusS NumZ NumZ = EqlS EqlZ
plusS NumZ (NumS b) = EqlS $ plusS NumZ b
plusS (NumS a) b = EqlS $ plusS a b

plusCommutes :: Natural a -> Natural b -> Equal (a :+: b) (b :+: a)
plusCommutes NumZ NumZ = EqlZ
plusCommutes NumZ (NumS b) = EqlS $ plusCommutes NumZ b
plusCommutes (NumS a) b = subst (EqlS $ plusCommutes a b) (plusS b a)

plus :: Natural a -> Natural b -> Natural (a :+: b)
plus NumZ b = b
plus (NumS a) b = NumS $ plus a b

mul :: Natural a -> Natural b -> Natural (a :*: b)
mul NumZ b = NumZ
mul (NumS a) b = plus b (mul a b)

-- This will also be helpful
zeroComm :: Natural a -> Equal Z (a :*: Z)
zeroComm NumZ = EqlZ
zeroComm (NumS n) = subst (plus' (zeroComm n) NumZ) plus_comm
  where
    plus_comm = plusCommutes (mul n NumZ) NumZ

lemma :: Equal a b -> Equal c d -> Equal (a :+: c) (b :+: d)
lemma EqlZ eq = eq
lemma (EqlS eq1) eq2 = EqlS $ lemma eq1 eq2

-- This is the proof that the kata requires.
-- | a * b = b * a
timesComm :: Natural a -> Natural b -> Equal (a :*: b) (b :*: a)
timesComm NumZ a = zeroComm a
timesComm a NumZ = symmetric $ zeroComm a
timesComm (NumS a) (NumS b) = subst (subst ab1 (symmetric comp)) (symmetric a1b)
  where
    ab_comm = timesComm a b -- a * b = b * a
    a1b_comm = timesComm (NumS a) b -- (S a) * b = b * (S a)
    ab1_comm = timesComm a (NumS b) -- a * (S b) = (S b) * a
    a1b_ab1 = plusS a b -- (S a) + b = a + (S b)
    a1b_ab1_comm = subst a1b_ab1 (plusCommutes a (NumS b)) -- (S a) + b = (S b) + a
    comp = lemma a1b_ab1_comm ab_comm -- ((S a) + b) + (a * b) = ((S b) + a) + (b * a)
    assc1 = plusAssoc (NumS a) b (mul a b) -- (S a) + (b + (a * b)) = ((S a) + b) + (a * b) => (S a) + (S a)*b = ((S a) + b) + (a * b)
    assc2 = plusAssoc (NumS b) a (mul b a) -- (S b) + (a + (b * a)) = ((S b) + a) + (b * a) => (S b) + (S b)*a = ((S b) + a) + (b * a)
    a1b_cop = lemma (reflexive (NumS a)) a1b_comm -- (S a) + (S a) * b = (S a) + b * (S a)
    ab1_cop = lemma (reflexive (NumS b)) ab1_comm -- (S b) + a * (S b) = (S b) + (S b) * a
    a1b = subst (symmetric a1b_cop) assc1 -- (S a) + b * (S a) = ((S a) + b) + (a * b)
    ab1 = subst ab1_cop assc2 -- (S b) + a * (S b) = ((S b) + a) + (b * a)
