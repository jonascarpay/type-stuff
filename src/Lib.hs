{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}

module Lib where

import Control.Monad (ap)

data Free f a
  = Pure a
  | Free (f (Free f a))
  deriving (Functor, Foldable, Traversable)

instance Functor f => Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance Functor f => Monad (Free f) where
  Pure a >>= fn = fn a
  Free f >>= fn = Free ((>>= fn) <$> f)

data Bind b a
  = B b
  | F a
  deriving (Eq, Show, Functor, Foldable, Traversable)

pattern B1 :: Bind () a
pattern B1 = B ()

type Bind1 = Bind ()

unbind :: (b -> r) -> (a -> r) -> (Bind b a -> r)
unbind fb _ (B b) = fb b
unbind _ fa (F a) = fa a

unbind1 :: r -> (a -> r) -> (Bind1 a -> r)
unbind1 r _ (B _) = r
unbind1 _ f (F a) = f a

abstract1 :: (Eq a, Functor f) => a -> f a -> f (Bind1 a)
abstract1 a = fmap $ \a' -> if a == a' then B () else F a'

instantiate1 :: Functor f => a -> f (Bind1 a) -> f a
instantiate1 a = fmap (unbind1 a id)

data Telescope f g a
  = Scope (f a) (Telescope f g (Bind1 a))
  | Nil (g a)
