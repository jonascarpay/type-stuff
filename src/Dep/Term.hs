{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}

module Dep.Term
  ( ValF (..),
    NeutF (..),
    Term (..),
    TermInfo (..),
    VF (..),
    FreeVars,
    resolve,
  )
where

import Control.Monad.Trans (lift)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.Map (Map)
import qualified Data.Map as Map
import Lib.Binder
import Lib.MMap (MMap, delete, singleton)

data ValF b f
  = Lam b f
  | PairV f f
  | PairT b f f
  | UnitV
  | UnitT
  | Star
  | Pi b f f
  deriving stock (Functor, Foldable, Traversable)

data NeutF v fn fv
  = Var v
  | App fn fv
  | Fst fn
  | Snd fn

data VF binder var val_v neut_n neut_v
  = Val (ValF binder val_v)
  | Neut (NeutF var neut_n neut_v)

newtype Term = Term (VF String String Term Term Term)

type FreeVars = MMap String Usage

data TermInfo = TermInfo
  { freeVars :: FreeVars,
    termInfo :: VF Binder Usage TermInfo TermInfo TermInfo
  }

data ResolveCtx = ResolveCtx
  { _depth :: Int,
    _bindings :: Map String Binder
  }

type Resolve = ReaderT ResolveCtx (State Int)

resolve :: Term -> TermInfo
resolve term0 = evalState (runReaderT (go term0) $ ResolveCtx 0 mempty) 0
  where
    bind :: String -> Resolve a -> Resolve (Binder, a)
    bind name inner = do
      ResolveCtx dep ctx <- ask
      n <- tick
      let binder = Binder name n dep (Map.lookup name ctx)
      inner' <- local (const $ ResolveCtx (succ dep) (Map.insert name binder ctx)) inner
      pure (binder, inner')

    tick :: Resolve Int
    tick = lift $ state $ \n -> (n, n + 1)
    go :: Term -> Resolve TermInfo
    go (Term term) = case term of
      Val vterm -> case vterm of
        Lam name body -> do
          (binder, body') <- bind name (go body)
          pure $ TermInfo (delete name $ freeVars body') (Val $ Lam binder body')
        PairV a b -> do
          a' <- go a
          b' <- go b
          pure $ TermInfo (freeVars a' <> freeVars b') (Val $ PairV a' b')
        PairT name a b -> do
          a' <- go a
          (binder, b') <- bind name (go b)
          pure $ TermInfo (freeVars a' <> freeVars b') (Val $ PairT binder a' b')
        Pi name a b -> do
          a' <- go a
          (binder, b') <- bind name (go b)
          pure $ TermInfo (freeVars a' <> freeVars b') (Val $ Pi binder a' b')
        UnitV -> pure (TermInfo mempty (Val UnitV))
        UnitT -> pure (TermInfo mempty (Val UnitT))
        Star -> pure (TermInfo mempty (Val Star))
      Neut nterm -> case nterm of
        Var var -> do
          ResolveCtx dep ctx <- ask
          n <- tick
          let usage = Usage var n (Map.lookup var ctx) dep
          pure $ TermInfo (singleton var usage) (Neut (Var usage))
        App f x -> do
          f' <- go f
          x' <- go x
          pure $ TermInfo (freeVars f' <> freeVars x') (Neut (App f' x'))
        Fst a -> do
          a' <- go a
          pure $ TermInfo (freeVars a') (Neut (Fst a'))
        Snd a -> do
          a' <- go a
          pure $ TermInfo (freeVars a') (Neut (Snd a'))
