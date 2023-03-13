{-# LANGUAGE DeriveTraversable #-}

module Lib.Free where

import Control.Monad (ap)

data Free f a
  = Pure a
  | F (f (Free f a))
  deriving (Functor, Foldable, Traversable)

instance Functor f => Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance Functor f => Monad (Free f) where
  Pure a >>= fn = fn a
  F f >>= fn = F ((>>= fn) <$> f)

foldM :: (Monad m, Traversable f) => (a -> m r) -> (f r -> m r) -> (Free f a -> m r)
foldM fa ff = go
  where
    go (Pure a) = fa a
    go (F k) = traverse go k >>= ff
