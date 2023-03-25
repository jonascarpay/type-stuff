{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM.FastCheck (inferT, infer) where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST, World)
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

{-# INLINE hole #-}
hole :: Depth -> UnifyBase s (TVar s)
hole depth = TVar <$> UF.fresh (TVHole depth)

{-# SPECIALIZE freshTy :: TypeF (TVar s) -> UnifyBase s (TVar s) #-}
freshTy :: MonadST m => TypeF (TVar (World m)) -> m (TVar (World m))
freshTy = fmap TVar . UF.fresh . TVTy

assertTV :: TVar s -> TypeF (TVar s) -> UnifyBase s ()
assertTV ta ty = do
  tb <- freshTy ty
  _ <- unifyTVar ta tb
  pure ()

{-# INLINE closeWith #-}
closeWith :: forall s a. (Depth -> TVar s -> Maybe a) -> TVar s -> UnifyBase s (Scheme a)
closeWith capFn root = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: StateT Int (UnifyBase s) Int
    tick = state $ \n -> (n, n + 1)
    go :: StateT Int (UnifyBase s) (Type (Either Int a))
    go = capture $ \fRaw ->
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

infer :: (a -> Scheme (TVar s)) -> Depth -> Term a -> UnifyBase s (TVar s)
infer ctx depth (Var a) = do
  let Scheme n h = ctx a
  vars <- replicateM n (hole depth)
  Free.foldM
    (either (\ix -> pure (vars !! ix)) pure)
    freshTy
    h
infer _ _ Unit = freshTy TUnit
infer _ _ (Int _) = freshTy TInt
infer ctx depth (Plus a b) = do
  va <- infer ctx depth a
  assertTV va TInt
  vb <- infer ctx depth b
  assertTV vb TInt
  freshTy TInt
infer ctx depth (App f x) = do
  vx <- infer ctx depth x
  vf <- infer ctx depth f
  vy <- hole depth
  -- TODO If I've analyzed this correctly, the reason we need the occurs checks of both unifyRec and close is because this next line creates an infinite type for \f. f f
  vf' <- freshTy (Arr vx vy)
  _ <- unifyTVar vf vf'
  pure vy
infer ctx depth (Let binding body) = do
  let depth' = succ depth
  tbody <- infer ctx depth' binding
  scheme <- close depth' tbody
  infer (unbind1 scheme ctx) depth body
infer ctx depth (Lam body) = do
  vx <- hole depth
  vy <- infer (unbind1 (singletonScheme vx) ctx) depth body
  freshTy (Arr vx vy)
infer ctx depth (Pair a b) = do
  ta <- infer ctx depth a
  tb <- infer ctx depth b
  freshTy (TPair ta tb)
infer ctx depth (LetRec binding body) = do
  let depth' = succ depth
  tbody' <- hole depth'
  tbody <- infer (unbind1 (singletonScheme tbody') ctx) depth' binding
  unifyTVar tbody tbody'
  scheme <- close depth' tbody
  infer (unbind1 scheme ctx) depth body

inferT :: Show a => Term a -> Either String (Type Int)
inferT term = runST $ runExceptT $ do
  closedTerm :: Term Void <- either (\vs -> throwError $ "Unbound variables: " <> show (toList vs)) pure $ closed term
  typ <- infer absurd (Depth 0) closedTerm
  Scheme _ t <- closeWith (\_ _ -> Nothing) typ
  pure $ either id absurd <$> t

runInfer :: Term Void -> Either String (Type Int)
runInfer term = runST $ runExceptT $ do
  typ <- infer absurd (Depth 0) term
  Scheme _ t <- closeWith (\_ _ -> Nothing) typ
  pure $ either id absurd <$> t
