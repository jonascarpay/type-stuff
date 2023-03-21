{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.ST.Class (MonadST (World, liftST))
import Control.Monad.State.Strict
import Data.Foldable (toList)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.String (IsString (..))
import Data.Void
import Lib.Free
import qualified Lib.Free as Free
import Lib.UF
import qualified Lib.UF as UF
import Rebound

data Term a
  = Var a
  | Lam (Term (Bind1 a))
  | App (Term a) (Term a)
  | Let (Term a) (Term (Bind1 a))
  | Int Int
  | Unit
  | Plus (Term a) (Term a)
  | Pair (Term a) (Term a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

instance Num (Term a) where
  fromInteger = Int . fromInteger
  (+) = Plus
  (*) = error "not implemented"
  (-) = error "not implemented"
  signum = error "not implemented"
  abs = error "not implemented"

instance IsString a => IsString (Term a) where
  fromString = Var . fromString

lam, λ :: Eq a => a -> Term a -> Term a
lam a = Lam . abstract1 a
λ = lam

infixl 9 @

(@) :: Term a -> Term a -> Term a
(@) = App

let' :: Eq a => a -> Term a -> Term a -> Term a
let' name bound body = Let bound (abstract1 name body)

data TypeF a
  = Arr a a
  | TPair a a
  | TInt
  | TUnit
  deriving (Eq, Show, Functor, Foldable, Traversable)

matchTypeF :: (a -> b -> c) -> TypeF a -> TypeF b -> Maybe (TypeF c)
matchTypeF f (Arr x1 y1) (Arr x2 y2) = pure $ Arr (f x1 x2) (f y1 y2)
matchTypeF f (TPair x1 y1) (TPair x2 y2) = pure $ Arr (f x1 x2) (f y1 y2)
matchTypeF _ TInt TInt = pure TInt
matchTypeF _ TUnit TUnit = pure TUnit
matchTypeF _ _ _ = Nothing

type Type = Free TypeF

newtype TVar s h = TVar (Point s (TVar' s h))

instance Unify (UnifyBase s) h' => Unify (UnifyBase s) (TVar s h') where
  unify (TVar a) (TVar b) = TVar <$> unify a b

-- TODO TVLift :: TVar' s h -> TVar' s (Bind1 h)
data TVar' s h = TVHole h | TVTy (TypeF (TVar s h))

instance Unify (UnifyBase s) a => Unify (UnifyBase s) (TypeF a) where
  unify a b = maybe (throwError "type check failure") sequence $ matchTypeF unify a b

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

{-# SPECIALIZE close :: TVar s (Bind1 a) -> Check s h (Scheme a) #-}
close :: forall m a. MonadST m => TVar (World m) (Bind1 a) -> m (Scheme a)
close tv = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: StateT Int m Int
    tick = state $ \n -> (n, n + 1)
    go :: StateT Int m (Type (Either Int a))
    go = captureM' $ \fRaw ->
      -- TODO detect infinite types
      let f :: TVar (World m) (Bind1 a) -> StateT Int m (Type (Either Int a))
          f (TVar p) = fRaw p $ \_ tv -> case tv of
            TVHole (Bound ()) -> pure . Left <$> tick
            TVHole (Free h) -> pure (pure (Right h))
            TVTy t -> Fix <$> traverse f t
       in f tv

instance (Applicative m, Unify m a, Unify m b) => Unify m (Bind a b) where
  unify (Bound a) (Bound b) = Bound <$> unify a b
  unify (Bound _) a = pure a
  unify a (Bound _) = pure a
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
  vf <- infer ctx f
  vy <- hole
  vf' <- freshTy (Arr vx vy)
  _ <- lift $ unify vf vf'
  pure vy
infer ctx (Let binding body) = do
  tbind <- withReaderT (const $ Bound ()) $ do
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

inferT :: Show a => Term a -> Either String (Type Int)
inferT term = runST $ runExceptT $ flip runReaderT (Bound ()) $ do
  closedTerm :: Term Void <- either (\vs -> throwError $ "Unbound variables: " <> show (toList vs)) pure $ closed term
  typ <- infer absurd closedTerm
  Scheme _ t <- lift $ close typ
  pure $ either id absurd <$> t

infer' :: Show a => Term a -> Type Char
infer' term = either error unScheme $ runST $ runExceptT $ flip runReaderT (Bound ()) $ do
  closedTerm <- either (\vs -> throwError $ "Unbound variables: " <> show (toList vs)) pure $ closed term
  typ <- infer absurd closedTerm
  lift $ close typ
  where
    unScheme :: Scheme Void -> Type Char
    unScheme (Scheme _ a) = either (chars !!) absurd <$> a
    chars :: String
    chars = "abcdefghijklmnopqrstuvwxyz"

subtype :: (Ord a, Eq b) => Type a -> Type b -> Bool
subtype tsub tsup = isJust $ flip runStateT mempty $ go tsub tsup
  where
    go :: (Ord a, Eq b) => Type a -> Type b -> StateT (Map a (Type b)) Maybe ()
    go (Pure a) b =
      gets (Map.lookup a) >>= \case
        Nothing -> modify (Map.insert a b)
        Just b' | b == b' -> pure ()
        _ -> empty
    go (Fix a) (Fix b) = maybe empty sequence_ $ matchTypeF go a b
    go (Fix _) (Pure _) = empty

infixr 9 -->

(-->) :: Type a -> Type a -> Type a
(-->) a b = Fix (Arr a b)
