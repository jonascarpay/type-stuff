{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.Instances.HM () where

import Control.Applicative
import HM.Term
import HM.Term.Embed (unit)
import HM.Type
import Test.QuickCheck
import qualified Test.QuickCheck as QC
import Test.QuickCheck.SafeGen
import qualified Test.QuickCheck.SafeGen as Safe

instance Arbitrary Term where
  arbitrary = do
    n <- arbitrary
    runSafeGen $ safeTerm n
  shrink (Term (Var v)) = unit : (Term . Var <$> shrink v)
  shrink (Term (Lam b v)) = [unit, v] <> [Term (Lam b' v) | b' <- shrink b] <> (Term . Lam b <$> shrink v)
  shrink (Term (App a b)) = [unit, a, b] <> (Term . App a <$> shrink b) <> [Term (App a' b) | a' <- shrink a]
  shrink (Term (Let v bi bo)) = [unit, bi, bo] <> [Term (Let v' bi bo) | v' <- shrink v]
  shrink (Term (LetRec bis bo)) = [unit, bo] <> (snd <$> bis) <> [Term (LetRec bis' bo) | bis' <- shrink bis] <> (Term . LetRec bis <$> shrink bo)
  shrink (Term Unit) = []
  shrink (Term (Plus a b)) = [unit, a, b] <> (Term . Plus a <$> shrink b) <> [Term (Plus a' b) | a' <- shrink a]
  shrink (Term (Pair a b)) = [unit, a, b] <> (Term . Pair a <$> shrink b) <> [Term (Pair a' b) | a' <- shrink a]
  shrink (Term (Lit n)) = unit : (Term . Lit <$> shrink n)

safeTerm :: Positive (Small Int) -> SafeGen Term
safeTerm (Positive (Small n_names)) = go n_names
  where
    name n = show <$> gen (chooseInt (0, n - 1))
    go :: Int -> SafeGen Term
    go n =
      Term
        <$> Safe.oneof
          [ Var <$> name n,
            Lam (show n) <$> go (n + 1),
            App <$> go n <*> go n,
            Let (show n) <$> go n <*> go (n + 1),
            Safe.oneof (letrec n <$> [0 .. 6])
          ]
    letrec :: Int -> Int -> SafeGen (TermF String String Term)
    letrec n n_binds = LetRec <$> sequenceA [(show ix,) <$> go (n + n_binds) | ix <- take n_binds [0 :: Int ..]] <*> go (n + n_binds)

instance Arbitrary1 TypeF where
  liftArbitrary arb0 =
    QC.frequency
      [ (1, pure TInt),
        (1, pure TUnit),
        (1, liftA2 TPair arb0 arb0),
        (3, liftA2 Arr arb0 arb0)
      ]
  liftShrink rec (Arr a b) = [Arr a' b | a' <- rec a] <> [Arr a' b | a' <- rec a]
  liftShrink rec (TPair a b) = [TPair a' b | a' <- rec a] <> [TPair a' b | a' <- rec a]
  liftShrink _ TInt = []
  liftShrink _ TUnit = []
