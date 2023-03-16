{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST (liftST))
import Control.Monad.State.Strict
import Data.Void
import Lib.Bind (Bind (..), Bind1, unbind1)
import Lib.Free
import qualified Lib.Free as Free
import Lib.UF
import qualified Lib.UF as UF

data Term a
  = Var a
  | Lam (Term (Bind1 a))
  | App (Term a) (Term a)
  | Let (Term a) (Term (Bind1 a))
  | Int Int
  | Unit
  | Plus (Term a) (Term a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

data TypeF a
  = Arr a a
  | TInt
  | TUnit
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Type = Free TypeF

newtype TVar s h = TVar (Point s (TVar' s h))

instance Unify (UnifyBase s) h' => Unify (UnifyBase s) (TVar s h') where
  unify (TVar a) (TVar b) = TVar <$> unify a b

-- TODO TVLift :: TVar' s h -> TVar' s (Bind1 h)
data TVar' s h = TVHole h | TVTy (TypeF (TVar s h))

instance Unify (UnifyBase s) a => Unify (UnifyBase s) (TypeF a) where
  unify (Arr x1 y1) (Arr x2 y2) = Arr <$> unify x1 x2 <*> unify y1 y2
  unify TInt TInt = pure TInt
  unify TUnit TUnit = pure TUnit
  unify _ _ = throwError "Type check failure"

instance Unify (UnifyBase s) h' => Unify (UnifyBase s) (TVar' s h') where
  unify (TVHole a) (TVHole b) = TVHole <$> unify a b
  unify (TVHole _) a = pure a
  unify a (TVHole _) = pure a
  unify (TVTy a) (TVTy b) = TVTy <$> unify a b

type UnifyBase s = ExceptT String (ST s)

type Check s h = ReaderT h (UnifyBase s)

-- TODO something cleverer than Int
data Scheme a
  = Scheme
      Int
      (Type (Either Int a))
  deriving (Show)

liftScheme :: a -> Scheme a
liftScheme tv = Scheme 0 (pure (Right tv))

liftScheme' :: forall s h. Scheme (TVar s h) -> ST s (Scheme (TVar1 s h))
liftScheme' (Scheme n t) = captureM' $ \fRaw ->
  let f :: TVar s h -> ST s (TVar1 s h)
      f (TVar p) = fRaw p $ \tvv tv -> case tv of
        TVHole h -> fmap TVar . fresh $ TVHole $ Free $ TVar tvv
        TVTy t -> do
          t' <- traverse f t
          fmap TVar $ fresh $ TVTy t'
   in Scheme n <$> (traverse . traverse) f t

hole :: Check s h (TVar s h)
hole = do
  h <- ask
  TVar <$> UF.fresh (TVHole h)

freshTy :: TypeF (TVar s h) -> Check s h (TVar s h)
freshTy = fmap TVar . UF.fresh . TVTy

assertTV :: Unify (UnifyBase s) h => TVar s h -> TypeF (TVar s h) -> Check s h ()
assertTV ta ty = do
  tb <- freshTy ty
  _ <- lift $ unify ta tb
  pure ()

type TVar1 s h = TVar s (Bind1 (TVar s h))

type Close s = StateT Int (UnifyBase s)

close :: forall s a. TVar s (Bind1 a) -> UnifyBase s (Scheme a)
close tv = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: Close s Int
    tick = state $ \n -> (n, n + 1)
    go :: Close s (Type (Either Int a))
    go = captureM' $ \fRaw ->
      -- TODO detect infinite types
      let f :: TVar s (Bind1 a) -> Close s (Type (Either Int a))
          f (TVar p) = fRaw p $ \_ tv -> case tv of
            TVHole (Bind ()) -> pure . Left <$> tick
            TVHole (Free h) -> pure (pure (Right h))
            TVTy t -> Fix <$> traverse f t
       in f tv

instance (Applicative m, Unify m a, Unify m b) => Unify m (Bind a b) where
  unify (Bind a) (Bind b) = Bind <$> unify a b
  unify (Bind _) a = pure a
  unify a (Bind _) = pure a
  unify (Free a) (Free b) = Free <$> unify a b

infer :: Unify (UnifyBase s) h => (a -> ST s (Scheme (TVar s h))) -> Term a -> Check s h (TVar s h)
infer ctx (Var a) = do
  Scheme n h <- liftST $ ctx a
  vars <- replicateM n hole
  Free.foldM
    (either (\ix -> pure (vars !! ix)) pure)
    freshTy
    h
infer _ Unit = freshTy TUnit
infer _ (Int _) = freshTy TInt
infer ctx (Plus a b) = do
  va <- infer ctx a
  assertTV va TInt
  vb <- infer ctx b
  assertTV vb TInt
  freshTy TInt
infer ctx (App f x) = do
  vx <- infer ctx x
  vy <- hole
  vf <- freshTy (Arr vx vy)
  vf' <- infer ctx f
  _ <- lift $ unify vf vf'
  pure vy
infer ctx (Let binding body) = do
  tbind <- withReaderT (const $ Bind ()) $ do
    infer (ctx >=> liftScheme') binding
  tbind' <- lift $ close tbind
  infer (unbind1 (pure tbind') ctx) body
infer ctx (Lam body) = do
  vx <- hole
  vy <- infer (unbind1 (pure $ liftScheme vx) ctx) body
  freshTy (Arr vx vy)

infer' :: Term Void -> Type Char
infer' t = either error unScheme $ runST $ runExceptT $ flip runReaderT (Bind ()) $ do
  t' <- infer absurd t
  lift $ close t'
  where
    unScheme :: Scheme Void -> Type Char
    unScheme (Scheme _ a) = either (chars !!) absurd <$> a
    chars :: String
    chars = "abcdefghijklmnopqrstuvwxyz"
