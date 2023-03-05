{-# LANGUAGE DeriveTraversable #-}

module HM where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Unify hiding (local)
import qualified Control.Unify as Unify
import Data.Foldable
import Data.Proxy
import Lib

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

-- newtype Scheme a = Scheme (Telescope Proxy Type a)

type Scheme s = Telescope Proxy TypeF (Point s)

data T s = Hole Int | Def (Telescope Proxy TypeF (Point s))

type Check s = ReaderT Int (ExceptT String (Unify s (T s)))

liftU :: Unify s (T s) a -> Check s a
liftU = lift . lift

freshHole :: Check s (Point s)
freshHole = do
  n <- ask
  liftU $ fresh (Hole n)

unifyP :: Point s -> Point s -> Check s ()
unifyP pa pb
  | pa == pb = pure ()
  | otherwise = do
      a <- liftU $ readPoint pa
      b <- liftU $ readPoint pb
      r <- unifyT a b
      liftU $ unify pa pb >> writePoint pa r

unifyT :: T s -> T s -> Check s (T s)
unifyT (Hole a) (Hole b) = pure $ Hole (min a b)
unifyT (Hole _) (Def t) = pure $ Def t
unifyT (Def t) (Hole _) = pure $ Def t
unifyT (Def a) (Def b) = Def <$> unifyTe a b

unifyTe :: Scheme s -> Scheme s -> Check s (Scheme s)
unifyTe (Scope _ a) b = do
  p <- freshHole
  unifyTe (instantiate1 p a) b
unifyTe a (Scope _ b) = do
  p <- freshHole
  unifyTe a (instantiate1 p b)
unifyTe (Nil a) (Nil b) = do
  n <- ask
  r <- unifyTy a b
  let open = toList r
  undefined

unifyTy :: TypeF (Point s) -> TypeF (Point s) -> Check s (TypeF (Point s))
unifyTy (Arr a1 b1) (Arr a2 b2) = do
  unifyP a1 a2
  unifyP b1 b2
  pure $ Arr a1 b1
unifyTy TInt TInt = pure TInt
unifyTy TUnit TUnit = pure TUnit
unifyTy a b = throwError $ "Couldn't match " <> show (void a) <> " with " <> show (void b)

infer :: Term (Point s) -> Point s -> Check s ()
infer (Var v) p = unifyP v p
infer (Lam b) p = do
  n <- ask
  px <- freshHole
  py <- freshHole
  pf <- liftU $ fresh (Def (Nil $ Arr px py))
  unifyP p pf
  local (+ 1) $ infer (instantiate1 px b) py
infer (App f x) py = do
  n <- ask
  px <- freshHole
  pf <- liftU $ fresh (Def (Nil $ Arr px py))
  infer f pf
  infer x px
infer (Int n) p = undefined
infer Unit p = undefined
infer (Plus a b) p = do
  pInt <- liftU $ fresh $ Def $ Nil TInt
  unifyP pInt p
  infer a pInt
  infer b pInt
