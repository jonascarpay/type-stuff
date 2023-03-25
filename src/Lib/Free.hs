{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module Lib.Free where

import Control.DeepSeq
import Control.Monad (ap)
import Data.String (IsString (..))
import GHC.Generics

data Free f a
  = Pure a
  | Fix (f (Free f a))
  deriving (Functor, Foldable, Traversable, Generic, Generic1)

instance IsString a => IsString (Free f a) where
  fromString = Pure . fromString

deriving instance (Eq a, forall x. Eq x => Eq (f x)) => Eq (Free f a)

instance (NFData a, forall x. NFData x => NFData (f x)) => NFData (Free f a)

instance (Show a, forall x. Show x => Show (f x)) => Show (Free f a) where
  showsPrec p (Pure a) = showsPrec p a
  showsPrec p (Fix f) = showsPrec p f

instance Functor f => Applicative (Free f) where
  pure = Pure
  (<*>) = ap

instance Functor f => Monad (Free f) where
  Pure a >>= fn = fn a
  Fix f >>= fn = Fix ((>>= fn) <$> f)

foldM :: (Monad m, Traversable f) => (a -> m r) -> (f r -> m r) -> (Free f a -> m r)
foldM fa ff = go
  where
    go (Pure a) = fa a
    go (Fix k) = traverse go k >>= ff
