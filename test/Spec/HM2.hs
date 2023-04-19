{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.HM2 where

import Control.Monad (replicateM)
import Data.Function (on)
import GHC.Generics
import HM2.Term as HM2
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.SafeGen
import qualified Test.QuickCheck.SafeGen as Safe

data RTerm a
  = RVar a
  | RLam (RTerm (Maybe a))
  | RApp (RTerm a) (RTerm a)
  | RLet (RTerm a) (RTerm (Maybe a))
  | RLetRec [RTerm (Either Int a)] (RTerm (Either Int a))
  deriving stock (Generic, Show, Eq, Functor)
  deriving (Arbitrary) via (FromSafeArbitrary (RTerm a))

instance SafeArbitrary a => SafeArbitrary (RTerm a) where
  safeArbitrary = rterm safeArbitrary

rterm :: forall a. SafeGen a -> SafeGen (RTerm a)
rterm f =
  Safe.oneof
    [ RVar <$> f,
      RLam <$> rterm mb,
      RApp <$> rterm f <*> rterm f,
      RLet <$> rterm f <*> rterm mb,
      Safe.oneof (letrec <$> [0 .. 6])
    ]
  where
    mb = Safe.frequency [(3, Just <$> f), (1, pure Nothing)]
    letrec :: Int -> SafeGen (RTerm a)
    letrec 0 = RLetRec [] <$> rterm (Right <$> f)
    letrec n =
      let e = Safe.frequency [(3, Right <$> f), (1, Left <$> gen (chooseInt (0, n - 1)))]
       in RLetRec <$> replicateM n (rterm e) <*> rterm e

safeTerm :: [String] -> SafeGen Term
safeTerm names = go
  where
    name = gen (elements names)
    go =
      Term
        <$> Safe.oneof
          [ Var <$> name,
            Lam <$> name <*> go,
            App <$> go <*> go,
            Let <$> name <*> go <*> go
          ]

abstract1 :: (Eq a, Functor f) => a -> f a -> f (Maybe a)
abstract1 a = fmap $ \a' -> if a == a' then Nothing else Just a'

fromTerm :: Term -> RTerm String
fromTerm (Term (Var v)) = RVar v
fromTerm (Term (Lam v b)) = RLam $ abstract1 v $ fromTerm b
fromTerm (Term (App a b)) = RApp (fromTerm a) (fromTerm b)
fromTerm (Term (Let v bi bo)) = RLet (fromTerm bi) (abstract1 v $ fromTerm bo)
fromTerm (Term (LetRec _ _)) = error "not implemented"

instance Arbitrary Term where
  arbitrary = do
    names <- arbitrary
    runSafeGen $ safeTerm (show . getSmall . getPositive <$> getNonEmpty names)
  shrink (Term (Var v)) = Term . Var <$> shrink v
  shrink (Term (Lam b v)) = [v] <> [Term (Lam b' v) | b' <- shrink b] <> (Term . Lam b <$> shrink v)
  shrink (Term (App a b)) = [a, b] <> (Term . App a <$> shrink b) <> [Term (App a' b) | a' <- shrink a]
  shrink (Term (Let _ bi bo)) = [bi, bo]
  shrink (Term (LetRec _ _)) = []

-- shrink = genericShrink

toTerm :: RTerm () -> Term
toTerm = go 1 (const 0)
  where
    lb :: Int -> String
    lb n = 'v' : show n
    go :: Int -> (a -> Int) -> RTerm a -> Term
    go _ ctx (RVar v) = Term $ Var (lb $ ctx v)
    go dep ctx (RLam body) =
      let dep' = dep + 1
       in Term $ Lam (lb dep') (go dep' (maybe dep ctx) body)
    go dep ctx (RApp a b) = Term $ App (go dep ctx a) (go dep ctx b)
    go dep ctx (RLet bind body) =
      let dep' = dep + 1
       in Term $ Let (lb dep') (go dep ctx bind) (go dep' (maybe dep ctx) body)
    go dep ctx (RLetRec binds body) =
      let dep' = dep + length binds
          go' = go dep' (either (dep +) ctx)
       in Term $ LetRec ((\(bind, n) -> (lb n, go' bind)) <$> zip binds [dep ..]) (go' body)

spec :: Spec
spec = modifyMaxDiscardRatio (const 100000000) . modifyMaxSuccess (const 1000) $ do
  prop "alpha" $ \(a :: RTerm ()) b ->
    (a == b) ==> on alphaEquivalent (resolve . toTerm) a b
  prop "alpha2" $ \(a :: Term) b ->
    on alphaEquivalent resolve a b ==> fromTerm a == fromTerm b

newtype SmallInt = SmallInt Int

instance Arbitrary SmallInt where
  arbitrary = SmallInt <$> choose (0, 4)
  shrink (SmallInt n) = SmallInt <$> take n [0 ..]