{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Instances () where

import Data.Foldable (toList)
import Lib.Free
import Spec.Instances.Free ()
import Spec.Instances.HM ()
import Test.QuickCheck

instance (Arbitrary a, Arbitrary1 f, Foldable f) => Arbitrary (Free f a) where
  arbitrary = sized go
    where
      go 0 = Pure <$> arbitrary
      go n = oneof [Pure <$> arbitrary, Fix <$> resize (div n 4 * 3) arbitrary1]
  shrink (Pure a) = Pure <$> shrink a
  shrink (Fix f) = toList f <> (Fix <$> shrink1 f)
