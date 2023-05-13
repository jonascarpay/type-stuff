{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Instances.Free where

import Control.Monad
import HM.Free.Term
import Rebound
import Test.QuickCheck
import Test.QuickCheck.SafeGen
import qualified Test.QuickCheck.SafeGen as Safe

instance (Arbitrary a, SafeArbitrary a) => Arbitrary (Term a) where
  arbitrary = runSafeGen safeArbitrary
  shrink (Var a) = Var <$> shrink a
  shrink (Lam body) = (Lam <$> shrink body) <> traverse (foldMap shrink) body
  shrink (App a b) = [a, b] <> (App a <$> shrink b) <> [App a' b | a' <- shrink a]
  shrink (Let bind body) = [bind, Lam body] <> (Let bind <$> shrink body) <> [Let bind' body | bind' <- shrink bind]
  shrink (LetRec bis bo) = (tolam <$> bis) <> [tolam bo] <> (flip LetRec bo <$> shrink bis) <> (LetRec bis <$> shrink bo)
    where
      tolam :: Term (Bind Int a) -> Term a
      tolam = Lam . fmap (unbind (const Bound1) Free)
  shrink (Pair a b) = [a, b] <> (Pair a <$> shrink b) <> [Pair a' b | a' <- shrink a]
  shrink (Plus a b) = [a, b] <> (Plus a <$> shrink b) <> [Plus a' b | a' <- shrink a]
  shrink Unit = []
  shrink (Int n) = Unit : (Int <$> shrink n)

instance SafeArbitrary b => SafeArbitrary (Term b) where
  safeArbitrary = rterm safeArbitrary
    where
      rterm :: forall a. SafeGen a -> SafeGen (Term a)
      rterm f =
        Safe.oneof
          [ Var <$> f,
            Lam <$> rterm mb,
            App <$> rterm f <*> rterm f,
            Let <$> rterm f <*> rterm mb,
            Safe.oneof (letrec <$> [0 .. 6]),
            Pair <$> rterm f <*> rterm f,
            Safe.oneof
              [ Int <$> safeArbitrary,
                pure Unit,
                Plus <$> rterm f <*> rterm f
              ]
          ]
        where
          mb = Safe.frequency [(3, Free <$> f), (1, pure Bound1)]
          letrec :: Int -> SafeGen (Term a)
          letrec 0 = LetRec [] <$> rterm (Right <$> f)
          letrec n =
            let e = Safe.frequency [(3, Right <$> f), (1, Left <$> gen (chooseInt (0, n - 1)))]
             in LetRec <$> replicateM n (rterm e) <*> rterm e
