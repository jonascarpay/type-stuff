{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM.Check (inferT) where

import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Void
import HM.Term
import HM.Type
import qualified Lib.Free as Free
import Lib.Match
import Lib.UF (Point)
import qualified Lib.UF as UF

type Unify s = ExceptT String (ST s)

type Depth = Word

data TVar' s = TVHole Depth | TVTy (TypeF (TVar s))

newtype TVar s = TVar {_unTVar :: Point s (TVar' s)}
  deriving newtype (Eq)

type TypeContext s = Map String (Scheme (TVar s))

hole :: Depth -> Unify s (TVar s)
hole depth = TVar <$> UF.fresh (TVHole depth)

fresh :: TypeF (TVar s) -> Unify s (TVar s)
fresh ty = TVar <$> UF.fresh (TVTy ty)

extend :: Binder -> Scheme (TVar s) -> TypeContext s -> TypeContext s
extend = Map.insert . binderName

extendMany :: [(Binder, Scheme (TVar s))] -> TypeContext s -> TypeContext s
extendMany bindings ctx = foldr (uncurry extend) ctx bindings

{-# INLINE closeWith #-}
closeWith :: forall s a. (Depth -> TVar s -> Maybe a) -> TVar s -> Unify s (Scheme a)
closeWith capFn root = uncurry (flip Scheme) <$> runStateT go 0
  where
    tick :: StateT Int (Unify s) Int
    tick = state $ \n -> (n, n + 1)
    go :: StateT Int (Unify s) (Type (Either Int a))
    go = UF.capture $ \fRaw ->
      let f :: [TVar s] -> TVar s -> StateT Int (Unify s) (Type (Either Int a))
          f prev (TVar p) = fRaw p $ \rep tv ->
            let rep' = TVar rep
             in case tv of
                  _ | elem rep' prev -> throwError "Infinite type!"
                  TVHole depth -> case capFn depth rep' of
                    Nothing -> pure . Left <$> tick
                    Just a -> pure $ pure $ pure a
                  TVTy t -> Free.Fix <$> traverse (f $ rep' : prev) t
       in f [] root

-- TODO Turn into wrapper with succ depth and hole
close :: Depth -> TVar s -> Unify s (Scheme (TVar s))
close thresh = closeWith $ \depth rep -> if depth >= thresh then Nothing else Just rep

unifyTVar :: forall s. TVar s -> TVar s -> Unify s ()
unifyTVar (TVar va) (TVar vb) = UF.unifyRec (throwError "Infinite type") f va vb
  where
    f :: (Point s (TVar' s) -> Point s (TVar' s) -> Unify s ()) -> TVar' s -> TVar' s -> Unify s (TVar' s)
    f _ (TVHole a) (TVHole b) = pure $ TVHole $ min a b
    f _ (TVHole _) (TVTy b) = pure (TVTy b)
    f _ (TVTy a) (TVHole _) = pure (TVTy a)
    f rec (TVTy a) (TVTy b) = case match (\(TVar p) (TVar q) -> TVar p <$ rec p q) a b of
      Just qq -> TVTy <$> sequence qq
      Nothing -> throwError "mismatch"

assert :: TVar s -> TypeF (TVar s) -> Unify s ()
assert ta ty = do
  tb <- fresh ty -- TODO can we get away without the allocation here?
  _ <- unifyTVar ta tb
  pure ()

infer :: TypeContext s -> Depth -> TermInfo -> Unify s (TVar s)
infer ctx depth (TermInfo _ t) = case t of
  Var (Usage v _ binder _) -> case binder of
    Nothing -> throwError $ "Unknown variable: " <> v
    Just b -> case Map.lookup (binderName b) ctx of
      -- We could just lookup on v here, but this way we get an extra sanity check
      -- that every bound variable also exists in the context
      Nothing -> error "Internal error; variable was bound but has no type?"
      Just (Scheme n h) -> do
        vars <- replicateM n (hole depth)
        Free.foldM
          (either (\ix -> pure (vars !! ix)) pure)
          fresh
          h
  Lam binder body -> do
    vx <- hole depth
    vy <- infer (extend binder (singletonScheme vx) ctx) depth body
    fresh (Arr vx vy)
  App f x -> do
    vx <- infer ctx depth x
    vf <- infer ctx depth f
    vy <- hole depth
    -- TODO If I've analyzed this correctly, the reason we need the occurs checks of both unifyRec and close is because this next line creates an infinite type for \f. f f
    vf' <- fresh (Arr vx vy)
    _ <- unifyTVar vf vf'
    pure vy
  Let binder binding body -> do
    let depth' = succ depth
    tbody <- infer ctx depth' binding
    scheme <- close depth' tbody
    infer (extend binder scheme ctx) depth body
  LetRec bindings body -> do
    -- see [ref:mutual_recursion_groups]
    let depth' = succ depth
        (binders, bindings') = unzip bindings
    tempVars <- replicateM (length bindings) (hole depth')
    let ctx' = extendMany (zip binders (singletonScheme <$> tempVars)) ctx
    forM_ (zip bindings' tempVars) $ \(binding, tempVar) -> do
      var <- infer ctx' depth' binding
      unifyTVar var tempVar
    schemes <- forM tempVars (close depth')
    infer (extendMany (zip binders schemes) ctx) depth body
  Unit -> fresh TUnit
  Lit _ -> fresh TInt
  Plus a b -> do
    va <- infer ctx depth a
    assert va TInt
    vb <- infer ctx depth b
    assert vb TInt
    fresh TInt
  Pair a b -> do
    ta <- infer ctx depth a
    tb <- infer ctx depth b
    fresh (TPair ta tb)

inferT :: TermInfo -> Either String (Type Int)
inferT term = runST $ runExceptT $ do
  typ <- infer mempty 0 term
  Scheme _ t <- closeWith (\_ _ -> Nothing) typ
  pure $ either id absurd <$> t
