{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Lib.Match where

import Control.Applicative
import GHC.Generics

class Traversable f => Match f where
  match :: (a -> b -> c) -> f a -> f b -> Maybe (f c)
  default match :: (Generic1 f, Match (Rep1 f)) => (a -> b -> c) -> f a -> f b -> Maybe (f c)
  {-# INLINE match #-}
  match f a b = to1 <$> match f (from1 a) (from1 b)

instance (Match f, Match g) => Match (f :+: g) where
  {-# INLINE match #-}
  match f (L1 l) (L1 r) = L1 <$> match f l r
  match f (R1 l) (R1 r) = R1 <$> match f l r
  match _ _ _ = Nothing

instance (Match f, Match g) => Match (f :.: g) where
  {-# INLINE match #-}
  match fn (Comp1 fg1) (Comp1 fg2) = match (match fn) fg1 fg2 >>= fmap Comp1 . sequenceA

instance (Match f, Match g) => Match (f :*: g) where
  {-# INLINE match #-}
  match f (l1 :*: r1) (l2 :*: r2) = liftA2 (:*:) (match f l1 l2) (match f r1 r2)

instance Match U1 where
  {-# INLINE match #-}
  match _ U1 U1 = pure U1

instance Match f => Match (M1 i c f) where
  {-# INLINE match #-}
  match f (M1 a) (M1 b) = M1 <$> match f a b

instance Match Par1 where
  {-# INLINE match #-}
  match f (Par1 a) (Par1 b) = pure $ Par1 (f a b)

instance Eq c => Match (K1 i c) where
  {-# INLINE match #-}
  match _ (K1 c1) (K1 c2)
    | c1 == c2 = Just (K1 c1)
    | otherwise = Nothing

deriving newtype instance Match f => Match (Rec1 f)

instance Match []

instance Eq b => Match ((,) b)
