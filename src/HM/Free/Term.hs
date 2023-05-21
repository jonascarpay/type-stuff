{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM.Free.Term where

import Control.DeepSeq (NFData)
import Data.Functor.Identity
import Data.List (elemIndex)
import GHC.Generics
import qualified HM.Term as HM
import Lib.Binder
import Rebound

data Term a
  = Var a
  | Lam (Term (Bind1 a))
  | App (Term a) (Term a)
  | Let (Term a) (Term (Bind1 a))
  | LetRec [Term (Bind Int a)] (Term (Bind Int a))
  | Int Int
  | Unit
  | Plus (Term a) (Term a)
  | Pair (Term a) (Term a)
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving anyclass (NFData)

fromTermF :: Ord v => HM.TermF v v (Term v) -> Term v
fromTermF (HM.Var v) = Var v
fromTermF (HM.Lam name body) = Lam $ abstract1 name body
fromTermF (HM.App a b) = App a b
fromTermF (HM.Let name bound body) = Let bound (abstract1 name body)
fromTermF (HM.LetRec binds body) = LetRec (fmap cap <$> binds') (cap <$> body)
  where
    (names, binds') = unzip binds
    cap str = case elemIndex str names of
      Just n -> Left n
      Nothing -> Right str
fromTermF (HM.Lit n) = Int n
fromTermF HM.Unit = Unit
fromTermF (HM.Pair a b) = Pair a b
fromTermF (HM.Plus a b) = Plus a b

fromTerm :: HM.Term -> Term String
fromTerm (HM.Term t) = fromTermF (fromTerm <$> t)

fromTermInfo :: HM.TermInfo -> Term String
fromTermInfo (HM.TermInfo _ t) = fromTermF (runIdentity $ HM.termFT (pure . binderName) (pure . varName) (pure . fromTermInfo) t)

toTerm :: Term String -> HM.Term
toTerm = go 0 id
  where
    lb :: Int -> String
    lb n = 'v' : show n
    go :: Int -> (a -> String) -> Term a -> HM.Term
    go _ ctx (Var v) = HM.Term $ HM.Var (ctx v)
    go dep ctx (Lam body) =
      let dep' = dep + 1
       in HM.Term $ HM.Lam (lb dep) (go dep' (unbind1 (lb dep) ctx) body)
    go dep ctx (App a b) = HM.Term $ HM.App (go dep ctx a) (go dep ctx b)
    go dep ctx (Let bind body) =
      let dep' = dep + 1
       in HM.Term $ HM.Let (lb dep) (go dep ctx bind) (go dep' (unbind1 (lb dep) ctx) body)
    go dep ctx (LetRec binds body) =
      let dep' = dep + length binds
          go' = go dep' (either (lb . (dep +)) ctx)
       in HM.Term $ HM.LetRec ((\(bind, n) -> (lb n, go' bind)) <$> zip binds [dep ..]) (go' body)
    go _ _ Unit = HM.Term HM.Unit
    go _ _ (Int n) = HM.Term (HM.Lit n)
    go dep ctx (Plus a b) = HM.Term (HM.Plus (go dep ctx a) (go dep ctx b))
    go dep ctx (Pair a b) = HM.Term (HM.Pair (go dep ctx a) (go dep ctx b))
