{-# LANGUAGE DerivingStrategies #-}
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
import Data.Foldable (toList)
import Data.Void
import HM.Term
import HM.Type
import Lib.Free
import qualified Lib.Free as Free
import Lib.Match
import Lib.UF
import qualified Lib.UF as UF
import Rebound

newtype TVar s h = TVar {unTVar :: Point s (TVar' s h)}
  deriving (Eq)

data TVar' s h = TVHole h | TVTy (TypeF (TVar s h))

type UnifyBase s = ExceptT String (ST s)

type Check s h =
  ReaderT
    (h, TVar s h -> TVar s h -> UnifyBase s ())
    (UnifyBase s)

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
        TVHole _ -> fmap TVar . fresh $ TVHole $ Free $ TVar tvv
        TVTy t -> do
          t' <- traverse f t
          fmap TVar $ fresh $ TVTy t'
   in Scheme n <$> (traverse . traverse) f t

hole :: Check s h (TVar s h)
hole = do
  h <- asks fst
  TVar <$> UF.fresh (TVHole h)

freshTy :: TypeF (TVar s h) -> Check s h (TVar s h)
freshTy = fmap TVar . UF.fresh . TVTy

assertTV :: TVar s h -> TypeF (TVar s h) -> Check s h ()
assertTV ta ty = do
  tb <- freshTy ty
  _ <- unifyTVar ta tb
  pure ()

unifyTVar :: TVar s h -> TVar s h -> Check s h ()
unifyTVar va vb = do
  f <- asks snd
  lift $ f va vb

type TVar1 s h = TVar s (Bind1 (TVar s h))

close :: forall s a. TVar s (Bind1 a) -> UnifyBase s (Scheme a)
close tv = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: StateT Int (UnifyBase s) Int
    tick = state $ \n -> (n, n + 1)
    go :: StateT Int (UnifyBase s) (Type (Either Int a))
    go = captureM' $ \fRaw ->
      -- TODO detect infinite types
      let f :: [TVar s (Bind1 a)] -> TVar s (Bind1 a) -> StateT Int (UnifyBase s) (Type (Either Int a))
          f prev p
            | p `elem` prev = throwError "Infinite type"
            | otherwise = fRaw (unTVar p) $ \_ tv -> case tv of
                TVHole (Bound ()) -> pure . Left <$> tick
                TVHole (Free h) -> pure (pure (Right h))
                TVTy t -> Fix <$> traverse (f $ p : prev) t
       in f [] tv

unifyTVarBase :: forall s h. (h -> h -> UnifyBase s h) -> TVar s h -> TVar s h -> UnifyBase s ()
unifyTVarBase fh (TVar va) (TVar vb) = unifyRec (throwError "Infinite type") f va vb
  where
    f :: (Point s (TVar' s h) -> Point s (TVar' s h) -> UnifyBase s ()) -> TVar' s h -> TVar' s h -> UnifyBase s (TVar' s h)
    f _ (TVHole a) (TVHole b) = TVHole <$> fh a b
    f _ (TVHole _) (TVTy b) = pure (TVTy b)
    f _ (TVTy a) (TVHole _) = pure (TVTy a)
    f rec (TVTy a) (TVTy b) = case match (\(TVar p) (TVar q) -> TVar p <$ rec p q) a b of
      Just qq -> TVTy <$> sequence qq
      Nothing -> throwError "mismatch"

infer :: (a -> ST s (Scheme (TVar s h))) -> Term a -> Check s h (TVar s h)
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
  vf <- infer ctx f
  vy <- hole
  vf' <- freshTy (Arr vx vy)
  _ <- unifyTVar vf vf'
  pure vy
infer ctx (Let binding body) = do
  tbind <- withReaderT (\(_, f) -> (Bound1, unifyTVarBase (unifyBindTVar f))) $ do
    infer (ctx >=> liftScheme') binding
  tbind' <- lift $ close tbind
  infer (unbind1 (pure tbind') ctx) body
infer ctx (Lam body) = do
  vx <- hole
  vy <- infer (unbind1 (pure $ liftScheme vx) ctx) body
  freshTy (Arr vx vy)
infer ctx (Pair a b) = do
  ta <- infer ctx a
  tb <- infer ctx b
  freshTy (TPair ta tb)

unifyBindTVar :: (TVar s h -> TVar s h -> UnifyBase s ()) -> Bind1 (TVar s h) -> Bind1 (TVar s h) -> UnifyBase s (Bind1 (TVar s h))
unifyBindTVar f (Free a) (Free b) = Free <$> (\p q -> p <$ f p q) a b
unifyBindTVar _ (Free a) Bound1 = pure $ Free a
unifyBindTVar _ Bound1 (Free b) = pure $ Free b
unifyBindTVar _ Bound1 Bound1 = pure Bound1

-- \f. f f
-- (f : v0) -> f f
-- (f : v0) -> ((f : v0) (f : v0) : v1)

inferT :: Show a => Term a -> Either String (Type Int)
inferT term = runST $ runExceptT $ runCheckBase $ do
  closedTerm :: Term Void <- either (\vs -> throwError $ "Unbound variables: " <> show (toList vs)) pure $ closed term
  typ <- infer absurd closedTerm
  Scheme _ t <- lift $ close typ
  pure $ either id absurd <$> t
  where
    runCheckBase :: Check s (Bind1 Void) a -> UnifyBase s a
    runCheckBase = flip runReaderT (Bound1, unifyTVarBase $ \_ _ -> pure Bound1)
