{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Counting where

import Counting.Preloaded
import Data.Coerce
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy
import Data.Void

-- https://www.codewars.com/kata/5b1bdc2bccef79e948000086
infinity :: Nat
infinity = S infinity

{- in Preloaded:
data Nat = Z | S Nat deriving (Show, Eq, Ord)
instance Num Nat -- so (2 :: Nat) == S (S Z)
instance Enum Nat -- so ([0..3] :: [Nat]) == [Z, S Z, S (S Z)]
instance Real Nat
instance Integral Nat -- so (2 ^ 3 :: Nat) == S (S (S (S (S (S (S (S Z)))))))
-}
-- newtype Identity a = Identity {runIdentity :: a}
-- newtype Const a b = Const {getConst :: a}
-- data Sum f g a = InL (f a) | InR (g a)
-- data Product f g a = Pair (f a) (g a)
-- newtype Compose f g a = Compose {getCompose :: f (g a)}
newtype Count x = Count
  { getCount :: Nat
  } deriving (Show, Eq, Ord)

-- | helper functions
mapC :: (Nat -> Nat) -> Count a -> Count b
mapC f (Count a) = Count $ f a

liftC2 :: (Nat -> Nat -> Nat) -> Count a -> Count b -> Count c
liftC2 f (Count a) (Count b) = Count $ f a b

coerceC :: Count a -> Count b
coerceC (Count a) = Count $ coerce a

-- | Countable
class Countable c where
  count :: Count c -- if you are using `Proxy` implement `count` from `count'` and vice versa
  -- count' :: Proxy c -> Count c
  -- count' = error "from count"

instance Countable Void where
  count = Count 0

instance Countable () where
  count = Count 1

instance Countable Bool where
  count = Count 2

instance Countable Nat where
  count = Count infinity

-- | Factor
class Factor f where
  factor :: Count c -> Count (f c) -- factor' :: Proxy f -> Count c -> Count (f c) -- optional

instance (Factor f, Countable c) => Countable (f c) where
  count = factor count

instance Factor Maybe where
  factor (Count x) = Count (x + 1)

instance Factor Identity where
  factor (Count x) = Count x

instance Factor Proxy where
  factor _ = Count 1

instance Factor Count where
  factor _ = Count infinity

instance Factor [] where
  factor (Count x) =
    Count
      (if x == 0
         then 1
         else infinity)

instance Countable c => Factor (Const c) where
  factor _ = coerceC (count :: Count c)

instance Countable c => Factor (Either c) where
  factor = liftC2 (+) (count :: Count c)

instance Countable c => Factor ((,) c) where
  factor = liftC2 (*) (count :: Count c)

instance Countable c => Factor ((->) c) where
  factor = liftC2 (flip (^)) (count :: Count c)

instance (Factor f, Factor g) => Factor (Sum f g) where
  factor (Count x) =
    liftC2
      (+)
      (factor (Count x) :: Count (f x))
      (factor (Count x) :: Count (g y))

instance (Factor f, Factor g) => Factor (Product f g) where
  factor (Count x) =
    liftC2
      (*)
      (factor (Count x) :: Count (f x))
      (factor (Count x) :: Count (g y))

instance (Factor f, Factor g) => Factor (Compose f g) where
  factor (Count x) =
    coerceC (factor (factor (Count x) :: Count (g x)) :: Count (f (g x)))

-- | Listable
class Countable a =>
      Listable a
  where
  list :: [a] -- list' :: Proxy a -> [a] -- optional

-- Data.List.genericLength (list :: [a]) `shouldBe` getCount (count :: Count a)
instance Listable Void where
  list = []

instance Listable () where
  list = [()]

instance Listable Bool where
  list = [False, True]

instance Listable Nat where
  list = 1 : (fmap S list)

instance Listable c => Listable (Maybe c) where
  list = Nothing : (fmap Just list)

instance Listable c => Listable [c] where
  list = [] : (fmap (list ++) list)

instance (Listable a, Listable b) => Listable (Either a b) where
  list = (fmap Left list) ++ (fmap Right list)

instance (Listable a, Listable b) => Listable (a, b) where
  list = [(x, y) | x <- list, y <- list]

instance (Eq a, Listable a, Listable b) => Listable (a -> b) where
  list =
    foldl
      (\f x ->
         [ (\arg ->
              if arg == x
                then y
                else f' arg)
         | y <- list
         , f' <- f
         ])
      [undefined]
      list
