{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.HM where

import Control.Applicative
import qualified Control.Exception as E
import Control.Monad
import Data.Foldable (toList)
import qualified HM.Check as Check
import qualified HM.FastCheck as Fast
import HM.Term
import HM.Type
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

spec :: Spec
spec = do
  describe "Subtyping" $ do
    prop "Every type t <: t" $ \(s :: Type Int) -> subtype s s
    prop "Every type t <: t with remapped variables" $ \(s :: Type Int) (Blind (f :: Int -> Int)) -> subtype s (f <$> s)
    prop "Every type t <: t with randomly instantiated variables" $ \(s :: Type Int) (Blind (f :: Int -> Type Int)) -> subtype s (s >>= f)
    prop "(∀ x. x) <: every type" $ \(s :: Type Int) -> subtype (pure ()) s
  describe "reference" $ mkSpec Check.inferT
  describe "faster" $ mkSpec Fast.inferT

mkSpec :: (Term String -> Either String (Type Int)) -> Spec
mkSpec infer = do
  describe "SKI Combinators" $ do
    it "I; λ x. x : a -> a" $
      checks
        (λ "x" "x")
        ("a" ~> "a")
    it "K; λ x y. x : a -> b -> a" $
      checks
        (λ "x" $ λ "y" "x")
        ("a" ~> "b" ~> "a")
    it "S; λ x y z. x z (y z) : (a -> b -> c) -> (a -> b) -> (a -> c)" $
      checks
        (λ "x" $ λ "y" $ λ "z" $ "x" @ "z" @ ("y" @ "z"))
        (("a" ~> "b" ~> "c") ~> ("a" ~> "b") ~> ("a" ~> "c"))
  describe "Polymorphism" $ do
    it "id id " $
      checks
        (let' "id" (λ "x" "x") ("id" @ "id"))
        ("a" ~> "a")
    it "let id x = x in (id, id)" $
      checks
        (let' "id" (λ "x" "x") (Pair "id" "id"))
        (tup ("a" ~> "a") ("b" ~> "b"))
    it "double CPS" $
      checks
        (λ "x" $ let' "cps" (λ "x" $ λ "f" $ "f" @ "x") $ Pair ("cps" @ "x") ("cps" @ "x"))
        ("r" ~> tup (("r" ~> "a") ~> "a") (("r" ~> "b") ~> "b"))
    it "CPS soup" $
      checks
        ( let'
            "cp"
            (λ "x" $ λ "f" $ let' "id" (λ "x" "x") $ "id" @ "f" @ Pair "x" ("id" @ "x"))
            "cp"
        )
        ("a" ~> (tup "a" "a" ~> "r") ~> "r")
    it "xor" $
      checks
        ( λ "a" . λ "b" $
            let' "false" (λ "a" $ λ "b" "b") $
              let' "true" (λ "a" $ λ "b" "a") $
                let' "not" (λ "a" $ "a" @ "false" @ "true") $
                  "a" @ ("not" @ "b") @ "b"
        )
        ( ("t1" ~> (("p1" ~> "p2" ~> "p2") ~> ("p3" ~> "p4" ~> "p3") ~> "t1") ~> "t2")
            ~> (("p1" ~> "p2" ~> "p2") ~> ("p3" ~> "p4" ~> "p3") ~> "t1")
            ~> "t2"
        )
    it "type variable scoping" $
      checks
        ( λ "a" $
            let'
              "withA"
              (λ "x" $ Pair "x" "a")
              ("withA" @ 0)
        )
        ("a" ~> tup (Fix TInt) "a")
  describe "letrec" $ do
    it "infinity" $ checks (letrec "speen" "speen" "speen") "a"
    it "fix" $ checks (letrec "fix" (λ "f" $ "f" @ ("fix" @ "f")) "fix") (("a" ~> "a") ~> "a")
    it "let s = s s in s" . typeError $ letrec "s" ("s" @ "s") "s"
  describe "Infinite types" $ do
    it "() ()" $ typeError (Unit @ Unit)
    it "λ f. f f" . typeError $
      λ "f" ("f" @ "f")
    it "Y = λ f. (λ x. f (x x)) (λ x. f (x x))" . typeError $
      λ "f" $
        λ "x" ("f" @ ("x" @ "x"))
          @ λ "x" ("f" @ ("x" @ "x"))
  it "explosion" . infers $ explode 10
  where
    checks :: Term String -> Type String -> Assertion
    checks term typ = do
      typ' <- either assertFailure pure $ infer term
      unless (subtype typ' typ && subtype typ typ') . E.throwIO $
        HUnitFailure Nothing $
          ExpectedButGot Nothing (show typ) (show typ')

    typeError :: Term String -> Assertion
    typeError term = case infer term of
      Left _ -> pure ()
      Right typ -> assertFailure $ "Unexpected success: " <> show typ

    infers :: Term String -> Assertion
    infers term = either assertFailure (const $ pure ()) $ infer term
