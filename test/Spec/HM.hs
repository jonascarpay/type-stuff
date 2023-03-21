{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.HM where

import Control.Applicative
import Data.Foldable (toList)
import HM
import Lib.Free
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

instance (Arbitrary a, Arbitrary1 f, Foldable f) => Arbitrary (Free f a) where
  arbitrary = sized go
    where
      go 0 = Pure <$> arbitrary
      go n = oneof [Pure <$> arbitrary, Fix <$> resize (div n 4 * 3) arbitrary1]
  shrink (Pure a) = Pure <$> shrink a
  shrink (Fix f) = toList f <> (Fix <$> shrink1 f)

instance Arbitrary1 TypeF where
  liftArbitrary arb =
    frequency
      [ (1, pure TInt),
        (1, pure TUnit),
        (1, liftA2 TPair arb arb),
        (3, liftA2 Arr arb arb)
      ]
  liftShrink rec (Arr a b) = [Arr a' b | a' <- rec a] <> [Arr a' b | a' <- rec a]
  liftShrink rec (TPair a b) = [TPair a' b | a' <- rec a] <> [TPair a' b | a' <- rec a]
  liftShrink _ TInt = []
  liftShrink _ TUnit = []

spec :: Spec
spec = do
  describe "Every type is a subtype of..." $ do
    prop "...itself" $ \(s :: Type Int) -> subtype s s
    prop "...itself with randomly remapped variables" $ \(s :: Type Int) (Blind (f :: Int -> Int)) -> subtype s (f <$> s)
    prop "...itself with randomly instantiated variables" $ \(s :: Type Int) (Blind (f :: Int -> Type Int)) -> subtype s (s >>= f)

-- describe "Unit tests" $ do
--   it "I : a -> a" _

-- it "S : (a -> b -> c) -> (a -> b) -> (a -> c)" _
