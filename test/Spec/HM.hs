{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.HM where

import qualified Control.Exception as E
import Control.Monad
import Data.Function (on)
import qualified HM.Free.Check as Check
import qualified HM.Free.FastCheck as Fast
import qualified HM.Free.Term as Free
import HM.Term
import HM.Term.Embed
import HM.Type
import Lib.Free
import Spec.Instances ()
import Test.HUnit
import Test.HUnit.Lang (FailureReason (ExpectedButGot), HUnitFailure (HUnitFailure))
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

spec :: Spec
spec = do
  describe "props" props
  describe "Subtyping" $ do
    prop "Every type t <: t" $ \(s :: Type Int) -> subtype s s
    prop "Every type t <: t with remapped variables" $ \(s :: Type Int) (Blind (f :: Int -> Int)) -> subtype s (f <$> s)
    prop "Every type t <: t with randomly instantiated variables" $ \(s :: Type Int) (Blind (f :: Int -> Type Int)) -> subtype s (s >>= f)
    prop "(∀ x. x) <: every type" $ \(s :: Type Int) -> subtype (pure ()) s
  describe "reference" $ mkSpec (Check.inferT . Free.fromTermInfo)
  describe "faster" $ mkSpec (Fast.inferT . Free.fromTermInfo)

props :: Spec
props = do
  prop "a α toTerm (fromTerm a)" $ \(a :: Term) ->
    on alphaEquivalent resolve a (Free.toTerm (Free.fromTerm a))
  prop "a α fromTerm (toTerm a)" $ \(a :: Free.Term String) ->
    a == Free.fromTerm (Free.toTerm a)
  prop "a α b == toTerm a α toTerm b" $ withMaxSuccess 10000 $ \(a :: Free.Term String) b ->
    (a == b) == on alphaEquivalent (resolve . Free.toTerm) a b
  prop "a α b == fromTerm a α fromTerm b" $ withMaxSuccess 10000 $ \(a :: Term) b ->
    on alphaEquivalent resolve a b == (Free.fromTerm a == Free.fromTerm b)

mkSpec :: (TermInfo -> Either String (Type Int)) -> Spec
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
  describe "other things" $ do
    it "on" $
      checks
        (λ "fc" $ λ "fb" $ λ "a0" $ λ "a1" $ "fc" @ ("fb" @ "a0") @ ("fb" @ "a1"))
        (("b" ~> "b" ~> "c") ~> ("a" ~> "b") ~> "a" ~> "a" ~> "c")
  describe "Polymorphism" $ do
    it "id id " $
      checks
        (let' "id" (λ "x" "x") ("id" @ "id"))
        ("a" ~> "a")
    it "let id x = x in (id, id)" $
      checks
        (let' "id" (λ "x" "x") (pair "id" "id"))
        (tup ("a" ~> "a") ("b" ~> "b"))
    it "double CPS" $
      checks
        (λ "x" $ let' "cps" (λ "x" $ λ "f" $ "f" @ "x") $ pair ("cps" @ "x") ("cps" @ "x"))
        ("r" ~> tup (("r" ~> "a") ~> "a") (("r" ~> "b") ~> "b"))
    it "CPS soup" $
      checks
        ( let'
            "cp"
            (λ "x" $ λ "f" $ let' "id" (λ "x" "x") $ "id" @ "f" @ pair "x" ("id" @ "x"))
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
              (λ "x" $ pair "x" "a")
              ("withA" @ 0)
        )
        ("a" ~> tup (Fix TInt) "a")
  describe "letrec" $ do
    it "infinity" $ checks (letrec1 "speen" "speen" "speen") "a"
    it "mutual infinity" $ checks (letrec [("a", "b"), ("b", "a")] "a") "a"
    it "fix" $ checks (letrec1 "fix" (λ "f" $ "f" @ ("fix" @ "f")) "fix") (("a" ~> "a") ~> "a")
    it "let s = s s in s" . typeError $ letrec1 "s" ("s" @ "s") "s"
    describe "mutual recursion fail demo" $ do
      -- [tag:mutual_recursion_fail_demo]
      -- see [ref:mutual_recursion_groups]
      it "exhibit A" . infers $
        letrec
          [("id", λ "x" "x")]
          (pair ("id" @ unit) ("id" @ 0))
      it "exhibit B" . typeError $
        letrec
          [ ("id", λ "x" "x"),
            ("a", pair ("id" @ unit) ("id" @ 0))
          ]
          "a"
  describe "Infinite types" $ do
    it "() ()" $ typeError (unit @ unit)
    it "λ f. f f" . typeError $
      λ "f" ("f" @ "f")
    it "Y = λ f. (λ x. f (x x)) (λ x. f (x x))" . typeError $
      λ "f" $
        λ "x" ("f" @ ("x" @ "x"))
          @ λ "x" ("f" @ ("x" @ "x"))
  it "explosion" . infers $ explodeLet 10
  where
    checks :: Term -> Type String -> Assertion
    checks term typ = do
      typ' <- either assertFailure pure $ infer (resolve term)
      unless (subtype typ' typ && subtype typ typ') . E.throwIO $
        HUnitFailure Nothing $
          ExpectedButGot Nothing (show typ) (show typ')

    typeError :: Term -> Assertion
    typeError term = case infer (resolve term) of
      Left _ -> pure ()
      Right typ -> assertFailure $ "Unexpected success: " <> show typ

    infers :: Term -> Assertion
    infers term = either assertFailure (const $ pure ()) $ infer (resolve term)
