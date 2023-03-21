{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.HM where

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad
import Data.Foldable (toList)
import HM
import Lib.Free
import Test.HUnit
import Test.HUnit.Lang (FailureReason (ExpectedButGot), HUnitFailure (HUnitFailure))
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

checks :: Term String -> Type String -> Assertion
checks term typ = do
  typ' <- either assertFailure pure $ inferT term
  unless (subtype typ' typ) . E.throwIO $
    HUnitFailure Nothing $
      ExpectedButGot Nothing (show typ) (show typ')

typeCheckFailure :: Term String -> Assertion
typeCheckFailure term = case inferT term of
  Left _ -> pure ()
  Right typ -> assertFailure $ "Unexpected success: " <> show typ

spec :: Spec
spec = do
  describe "Subtyping" $ do
    prop "Every type t <: t" $ \(s :: Type Int) -> subtype s s
    prop "Every type t <: t with remapped variables" $ \(s :: Type Int) (Blind (f :: Int -> Int)) -> subtype s (f <$> s)
    prop "Every type t <: t with randomly instantiated variables" $ \(s :: Type Int) (Blind (f :: Int -> Type Int)) -> subtype s (s >>= f)
    prop "(∀ x. x) <: every type" $ \(s :: Type Int) -> subtype (pure ()) s
  describe "SKI Combinators" $ do
    it "I; λ x. x : a -> a" $
      checks
        (λ "x" "x")
        ("a" --> "a")
    it "K; λ x y. x : a -> b -> a" $
      checks
        (λ "x" $ λ "y" "x")
        ("a" --> "b" --> "a")
    it "S; λ x y z. x z (y z) : (a -> b -> c) -> (a -> b) -> (a -> c)" $
      checks
        (λ "x" $ λ "y" $ λ "z" $ "x" @ "z" @ ("y" @ "z"))
        (("a" --> "b" --> "c") --> ("a" --> "b") --> ("a" --> "c"))
  describe "Type check failures" $ do
    it "() ()" $ typeCheckFailure (Unit @ Unit)
    it "λ f. f f" . typeCheckFailure $
      λ "f" ("f" @ "f")
    it "Y = λ f. (λ x. f (x x)) (λ x. f (x x))" . typeCheckFailure $
      λ "f" $
        λ "x" ("f" @ ("x" @ "x"))
          @ λ "x" ("f" @ ("x" @ "x"))
