{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Spec.HM2 where

import Control.Monad (replicateM)
import Data.Function (on)
import Data.List (elemIndex)
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
  deriving stock (Generic, Show, Eq, Functor, Foldable, Traversable)

instance (Arbitrary a, SafeArbitrary a) => Arbitrary (RTerm a) where
  arbitrary = runSafeGen safeArbitrary
  shrink (RVar a) = RVar <$> shrink a
  shrink (RLam body) = (RLam <$> shrink body) <> traverse (foldMap shrink) body
  shrink (RApp a b) = [a, b] <> (RApp a <$> shrink b) <> [RApp a' b | a' <- shrink a]
  shrink (RLet bind body) = [bind, RLam body] <> (RLet bind <$> shrink body) <> [RLet bind' body | bind' <- shrink bind]
  shrink (RLetRec bis bo) = (tolam <$> bis) <> [tolam bo] <> (flip RLetRec bo <$> shrink bis) <> (RLetRec bis <$> shrink bo)
    where
      tolam :: RTerm (Either Int a) -> RTerm a
      tolam = RLam . fmap (either (const Nothing) Just)

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

abstract1 :: (Eq a, Functor f) => a -> f a -> f (Maybe a)
abstract1 a = fmap $ \a' -> if a == a' then Nothing else Just a'

fromTerm :: Term -> RTerm String
fromTerm (Term (Var v)) = RVar v
fromTerm (Term (Lam v b)) = RLam $ abstract1 v $ fromTerm b
fromTerm (Term (App a b)) = RApp (fromTerm a) (fromTerm b)
fromTerm (Term (Let v bi bo)) = RLet (fromTerm bi) (abstract1 v $ fromTerm bo)
fromTerm (Term (LetRec binds body)) = RLetRec (fmap cap . fromTerm <$> binds') (cap <$> fromTerm body)
  where
    (names, binds') = unzip binds
    cap :: String -> Either Int String
    cap str = case elemIndex str names of
      Just n -> Left n
      Nothing -> Right str

instance Arbitrary Term where
  arbitrary = do
    n <- arbitrary
    runSafeGen $ safeTerm n
  shrink (Term (Var v)) = Term . Var <$> shrink v
  shrink (Term (Lam b v)) = [v] <> [Term (Lam b' v) | b' <- shrink b] <> (Term . Lam b <$> shrink v)
  shrink (Term (App a b)) = [a, b] <> (Term . App a <$> shrink b) <> [Term (App a' b) | a' <- shrink a]
  shrink (Term (Let v bi bo)) = [bi, bo] <> [Term (Let v' bi bo) | v' <- shrink v]
  shrink (Term (LetRec bis bo)) = [bo] <> (snd <$> bis) <> [Term (LetRec bis' bo) | bis' <- shrink bis] <> (Term . LetRec bis <$> shrink bo)

toTerm :: RTerm String -> Term
toTerm = go 0 id
  where
    lb :: Int -> String
    lb n = 'v' : show n
    go :: Int -> (a -> String) -> RTerm a -> Term
    go _ ctx (RVar v) = Term $ Var (ctx v)
    go dep ctx (RLam body) =
      let dep' = dep + 1
       in Term $ Lam (lb dep) (go dep' (maybe (lb dep) ctx) body)
    go dep ctx (RApp a b) = Term $ App (go dep ctx a) (go dep ctx b)
    go dep ctx (RLet bind body) =
      let dep' = dep + 1
       in Term $ Let (lb dep) (go dep ctx bind) (go dep' (maybe (lb dep) ctx) body)
    go dep ctx (RLetRec binds body) =
      let dep' = dep + length binds
          go' = go dep' (either (lb . (dep +)) ctx)
       in Term $ LetRec ((\(bind, n) -> (lb n, go' bind)) <$> zip binds [dep ..]) (go' body)

spec :: Spec
spec = do
  prop "a α toTerm (fromTerm a)" $ \(a :: Term) ->
    on alphaEquivalent resolve a (toTerm (fromTerm a))
  prop "a α fromTerm (toTerm a)" $ \(a :: RTerm String) ->
    a == fromTerm (toTerm a)
  prop "a α b == toTerm a α toTerm b" $ withMaxSuccess 10000 $ \(a :: RTerm String) b ->
    (a == b) == on alphaEquivalent (resolve . toTerm) a b
  prop "a α b == fromTerm a α fromTerm b" $ withMaxSuccess 10000 $ \(a :: Term) b ->
    on alphaEquivalent resolve a b == (fromTerm a == fromTerm b)
