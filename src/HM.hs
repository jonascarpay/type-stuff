{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module HM where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.State.Strict
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
  deriving (Unify (Check s h))

data TVar' s h = TVHole h | TVTy (TypeF (TVar s h))

instance Unify (Check s h) a => Unify (Check s h) (TypeF a) where
  unify (Arr x1 y1) (Arr x2 y2) = Arr <$> unify x1 x2 <*> unify y1 y2
  unify TInt TInt = pure TInt
  unify TUnit TUnit = pure TUnit
  unify _ _ = throwError "Type check failure"

instance Unify (Check s h) (TVar' s h) where
  unify (TVHole _) a = pure a
  unify a (TVHole _) = pure a
  unify (TVTy a) (TVTy b) = TVTy <$> unify a b

type Check s h = ReaderT h (ExceptT String (ST s))

-- TODO something cleverer than Int
data Scheme s h
  = Scheme
      Int
      (Type (Either Int (TVar s h)))

liftScheme :: TVar s h -> Scheme s h
liftScheme tv = Scheme 0 (pure (Right tv))

hole :: Check s h (TVar s h)
hole = do
  h <- ask
  TVar <$> UF.fresh (TVHole h)

freshTy :: TypeF (TVar s h) -> Check s h (TVar s h)
freshTy = fmap TVar . UF.fresh . TVTy

assertTV :: TVar s h -> TypeF (TVar s h) -> Check s h ()
assertTV ta ty = do
  tb <- freshTy ty
  _ <- unify ta tb
  pure ()

type TVar1 s h = TVar s (Bind1 (TVar s h))

type Close s h = StateT Int (Check s h)

close :: TVar s (Bind1 (TVar s h)) -> Check s h (Scheme s h)
close tv = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: Close s h Int
    tick = state $ \n -> (n, n + 1)
    go :: Close s h (Type (Either Int (TVar s h)))
    go = captureM' $ \f ->
      let f' :: TVar' s (Bind1 (TVar s h)) -> Close s h (Type (Either Int (TVar s h)))
          f' (TVHole (Bind ())) = pure . Left <$> tick
          f' (TVHole (Lib.Bind.Free h)) = pure $ pure $ pure h
          f' (TVTy t) = _ t
       in _

infer :: (a -> Scheme s h) -> Term a -> Check s h (TVar s h)
infer ctx (Var a) = do
  let Scheme n h = ctx a
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
  _ <- unify vf vf'
  pure vy
infer ctx (Let binding body) = do
  tbind <- withReaderT (const $ Bind ()) $ do
    infer _ binding
  tbind' <- close tbind
  undefined
infer ctx (Lam body) = do
  vx <- hole
  vy <- infer (unbind1 (liftScheme vx) ctx) body
  freshTy (Arr vx vy)
