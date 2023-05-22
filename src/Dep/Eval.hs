{-# LANGUAGE LambdaCase #-}

module Dep.Eval where

import Control.Monad.ST
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except
import Data.Map
import qualified Data.Map as Map
import Data.STRef
import Dep.Term
import Lib.Binder
import Lib.MMap (MMap (..))

newtype Value s = Value (STRef s (Value' s))

data Closure s
  = Closure
      (Context s)
      (VF Binder Usage TermInfo TermInfo TermInfo)

data Value' s
  = Con (WHNF s)
  | BlackHole
  | Thunk (Closure s)

type WHNF s = ValF Binder (Closure s)

type Context s = Map String (Value s) -- TODO use id's or something

type Eval s = ExceptT String (ST s)

liftST :: ST s a -> Eval s a
liftST = lift

force :: Value s -> Eval s (WHNF s)
force (Value ref) =
  liftST (readSTRef ref) >>= \case
    Con w -> pure w
    BlackHole -> throwE "Infinite recursion!"
    Thunk c -> do
      liftST $ writeSTRef ref BlackHole
      r <- eval c
      liftST $ writeSTRef ref (Con r)
      pure r

mkThunk :: Closure s -> Eval s (Value s)
mkThunk = fmap Value . liftST . newSTRef . Thunk

-- TODO we might not need to bother with filtering.
-- might lead to memory leaks? Also see [ref:re-close]
close :: Context s -> TermInfo -> Closure s
close ctx (TermInfo (MMap fvs) term) =
  let ctx' = Map.mapMaybeWithKey (\fv _ -> Map.lookup fv ctx) fvs
   in Closure ctx' term

-- Document that the context should be allowed to contain too much
eval :: Closure s -> Eval s (WHNF s)
eval (Closure ctx term0) = case term0 of
  Val v0 -> pure $ close ctx <$> v0
  Neut n0 -> case n0 of
    Var v -> case Map.lookup (varName v) ctx of
      Nothing -> throwE $ "Unbound variable: " <> varName v
      Just val -> force val
    App f x ->
      eval (close ctx f {- [ref:re-close] -}) >>= \case
        Lam binder (Closure bodyCtx body) -> do
          x_thunk <- mkThunk (close ctx x)
          let bodyCtx' = Map.insert (binderName binder) x_thunk bodyCtx
          eval $ Closure bodyCtx' body
        _ -> throwE "Runtime error! Applying to a not-a-function"
    Fst body ->
      eval (close ctx body {- [ref:re-close] -}) >>= \case
        PairV c _ -> eval c
        _ -> throwE "Runtime error! Taking fst of a not-a-pair"
    Snd body ->
      eval (close ctx body {- [ref:re-close] -}) >>= \case
        PairV _ c -> eval c
        _ -> throwE "Runtime error! Taking fst of a not-a-pair"

-- [tag:re-close]
-- It shouldn't be necessary to close the sub-expression, we should be able to just pass the outer context.
-- Doing so will mean there might be more values in the context than are required, but that shouldn't matter, and closing can be pretty slow.
