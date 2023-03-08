{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module HM where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
import Control.Monad.State.Strict
import Data.Foldable
import Data.Proxy
import Lib
import Lib.UF

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

type Check s h = ReaderT h (ExceptT String (ST s))

hole :: Check s h h
hole = undefined

data T s h = Hole h | Def (Scheme h)

type Scheme = Telescope Proxy TypeF

type TVar s h = Point s (T s h)

type TVar1 s h = TVar s (Bind1 (TVar s h))

closeS :: Scheme (TVar1 s h) -> Check s h (Scheme (Bind1 (TVar s h)))
closeS = traverse closeV

closeV :: TVar s (Bind1 (TVar s h)) -> Check s h (Bind1 (TVar s h))
closeV p =
  desc p >>= \case
    Hole (B ()) -> pure B1
    Hole (F h) -> pure $ F h
    Def sch -> _ sch

foo :: Scheme (Bind1 (TVar1 s h)) -> Check s h (Bind1 (TVar s h))
foo sch = do
  v <- fresh $ Def $ _ sch
  pure $ F v

-- closeT :: T s (Bind1 (TVar s h)) -> Check s h (Bind1 (T s h))
-- closeT (Hole (F h)) = pure (F $ Hole h)
-- closeT (Hole B1) = pure B1
-- closeT (Def sch) = _ sch

{--
type Type = Free TypeF

-- newtype Scheme a = Scheme (Telescope Proxy Type a)

type TVar s = Point s (T s)

type Scheme s = Telescope Proxy TypeF (TVar s)

data T s = Hole Int | Def (Scheme s)

type Check s = ReaderT Int (ExceptT String (ST s))

-- unifyV :: TVar s ->

freshHole :: Check s (TVar s)
freshHole = do
  n <- ask
  fresh (Hole n)

unifyP :: TVar s -> TVar s -> Check s ()
unifyP = unifyWith unifyT

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

unifyTy :: TypeF (TVar s) -> TypeF (TVar s) -> Check s (TypeF (TVar s))
unifyTy (Arr a1 b1) (Arr a2 b2) = do
  unifyP a1 a2
  unifyP b1 b2
  pure $ Arr a1 b1
unifyTy TInt TInt = pure TInt
unifyTy TUnit TUnit = pure TUnit
unifyTy a b = throwError $ "Couldn't match " <> show (void a) <> " with " <> show (void b)

close :: T s -> Check s (T s)
close s = do
  lvl <- ask
  (s', n) <- runStateT (capture (fT lvl) s) 0
  pure $ close' n s'
  where
    fT :: Int -> T s -> StateT Int (Check s) (Maybe Int)
    fT lvl (Hole n) | n >= lvl = state $ \c -> (Just c, c + 1)
    fT _ _ = pure Nothing
    close' :: Int -> Telescope Proxy TypeF (Either Int a) -> Telescope Proxy TypeF a
    close' n sc = go n (\wrap fi fa -> wrap (either fi fa <$> sc))
    go ::
      Int ->
      ( forall r.
        (Telescope Proxy TypeF r -> Telescope Proxy TypeF a) ->
        (Int -> r) ->
        (a -> r) ->
        q
      ) ->
      q
    go 0 k = k id (\x -> error $ "indexError: " <> show x) id
    go n k =
      let n' = n - 1
       in go n' (\w fi fa -> k (w . Scope Proxy) (\x -> if x == n' then B1 else F (fi x)) (F . fa))

mapV :: (Scheme s -> Check s (Scheme s)) -> TVar s -> Check s ()
mapV f v = undefined

-- TODO Term (TVar s) -> Check (T s)
infer :: Term (TVar s) -> TVar s -> Check s ()
infer (Var v) p = unifyP v p
infer (Lam b) p = do
  n <- ask
  px <- freshHole
  py <- freshHole
  pf <- fresh (Def (Nil $ Arr px py))
  unifyP p pf
  infer (instantiate1 px b) py
infer (App f x) py = do
  n <- ask
  px <- freshHole
  pf <- fresh (Def (Nil $ Arr px py))
  infer f pf
  infer x px
infer (Int n) p = undefined
infer Unit p = undefined
infer (Plus a b) p = do
  pInt <- fresh $ Def $ Nil TInt
  unifyP pInt p
  infer a pInt
  infer b pInt
infer (Let bind body) p = do
  vbind <- local (+ 1) $ do
    vbind <- freshHole
    infer bind vbind
    pure vbind
  infer (instantiate1 vbind body) p
-}
