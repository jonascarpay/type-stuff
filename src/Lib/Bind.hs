{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}

module Lib.Bind where

data Bind b a
  = Bind b
  | Free a
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative (Bind b) where
  pure = Free
  Free f <*> Free a = Free (f a)
  Bind b <*> _ = Bind b
  _ <*> Bind b = Bind b

pattern B1 :: Bind () a
pattern B1 = Bind ()

type Bind1 = Bind ()

unbind :: (b -> r) -> (a -> r) -> (Bind b a -> r)
unbind fb _ (Bind b) = fb b
unbind _ fa (Free a) = fa a

unbind1 :: r -> (a -> r) -> (Bind1 a -> r)
unbind1 r _ (Bind _) = r
unbind1 _ f (Free a) = f a

abstract1 :: (Eq a, Functor f) => a -> f a -> f (Bind1 a)
abstract1 a = fmap $ \a' -> if a == a' then Bind () else Free a'

instantiate1 :: Functor f => a -> f (Bind1 a) -> f a
instantiate1 a = fmap (unbind1 a id)
