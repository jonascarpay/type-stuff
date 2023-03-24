{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM.FastCheck (inferT, Scheme (..)) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
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

newtype TVar s = TVar {_unTVar :: Point s (TVar' s)}
  deriving (Eq)

newtype Depth = Depth Word
  deriving newtype (Enum, Eq, Ord)

data TVar' s = TVHole Depth | TVTy (TypeF (TVar s))

type UnifyBase s = ExceptT String (ST s)

type Check s =
  ReaderT
    Depth
    (UnifyBase s)

data Scheme a
  = Scheme
      Int
      (Type (Either Int a))
  deriving (Show)

hole :: Check s (TVar s)
hole = do
  h <- ask
  TVar <$> UF.fresh (TVHole h)

freshTy :: TypeF (TVar s) -> Check s (TVar s)
freshTy = fmap TVar . UF.fresh . TVTy

assertTV :: TVar s -> TypeF (TVar s) -> Check s ()
assertTV ta ty = do
  tb <- freshTy ty
  _ <- lift $ unifyTVar ta tb
  pure ()

{-# INLINE closeWith #-}
closeWith :: forall s a. (Depth -> TVar s -> Maybe a) -> TVar s -> UnifyBase s (Scheme a)
closeWith capFn root = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: StateT Int (UnifyBase s) Int
    tick = state $ \n -> (n, n + 1)
    go :: StateT Int (UnifyBase s) (Type (Either Int a))
    go = captureM' $ \fRaw ->
      let f :: [TVar s] -> TVar s -> StateT Int (UnifyBase s) (Type (Either Int a))
          f prev (TVar p) = fRaw p $ \rep tv ->
            let rep' = TVar rep
             in case tv of
                  _ | elem rep' prev -> throwError "Infinite type!"
                  TVHole depth -> case capFn depth rep' of
                    Nothing -> pure . Left <$> tick
                    Just a -> pure $ pure $ pure a
                  TVTy t -> Fix <$> traverse (f $ rep' : prev) t
       in f [] root

close :: Depth -> TVar s -> UnifyBase s (Scheme (TVar s))
close thresh = closeWith $ \depth rep -> if depth >= thresh then Nothing else Just rep

unifyTVar :: forall s. TVar s -> TVar s -> UnifyBase s ()
unifyTVar (TVar va) (TVar vb) = unifyRec (throwError "Infinite type") f va vb
  where
    f :: (Point s (TVar' s) -> Point s (TVar' s) -> UnifyBase s ()) -> TVar' s -> TVar' s -> UnifyBase s (TVar' s)
    f _ (TVHole a) (TVHole b) = pure $ TVHole $ min a b
    f _ (TVHole _) (TVTy b) = pure (TVTy b)
    f _ (TVTy a) (TVHole _) = pure (TVTy a)
    f rec (TVTy a) (TVTy b) = case match (\(TVar p) (TVar q) -> TVar p <$ rec p q) a b of
      Just qq -> TVTy <$> sequence qq
      Nothing -> throwError "mismatch"

infer :: (a -> Scheme (TVar s)) -> Term a -> Check s (TVar s)
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
  vf <- infer ctx f
  vy <- hole
  vf' <- freshTy (Arr vx vy)
  _ <- lift $ unifyTVar vf vf'
  pure vy
infer ctx (Let binding body) = do
  -- TODO make a test case that fails on s/succ/id
  tbind <- withReaderT succ $ do
    t <- infer ctx binding
    dep <- ask
    lift $ close dep t
  infer (unbind1 tbind ctx) body
infer ctx (Lam body) = do
  vx <- hole
  vy <- infer (unbind1 (singletonScheme vx) ctx) body
  freshTy (Arr vx vy)
infer ctx (Pair a b) = do
  ta <- infer ctx a
  tb <- infer ctx b
  freshTy (TPair ta tb)

singletonScheme :: a -> Scheme a
singletonScheme tv = Scheme 0 (pure (Right tv))

inferT :: Show a => Term a -> Either String (Type Int)
inferT term = runST $ runExceptT $ runCheckBase $ do
  closedTerm :: Term Void <- either (\vs -> throwError $ "Unbound variables: " <> show (toList vs)) pure $ closed term
  typ <- infer absurd closedTerm
  Scheme _ t <- lift $ closeWith (\_ _ -> Nothing) typ
  pure $ either id absurd <$> t
  where
    runCheckBase :: Check s a -> UnifyBase s a
    runCheckBase = flip runReaderT (Depth 0)
