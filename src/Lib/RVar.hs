{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib.RVar where

import Control.Monad
import Control.Monad.Except
import Control.Monad.ST.Class (MonadST (World))
import Lib.UF

newtype RVar s f = RVar (Point s (f (RVar s f)))
  deriving (Eq)

data UnificationFailure
  = InfiniteType
  | Mismatch
  | Scope

type UnifyT = ExceptT UnificationFailure

class Traversable f => Unify1 m f where
  unify1 :: (a -> a -> UnifyT m a) -> f a -> f a -> UnifyT m (f a)

unifyRec ::
  forall f m.
  (Unify1 m f, MonadST m) =>
  RVar (World m) f ->
  RVar (World m) f ->
  UnifyT m ()
unifyRec = go []
  where
    go ::
      [Point (World m) (f (RVar (World m) f))] ->
      RVar (World m) f ->
      RVar (World m) f ->
      UnifyT m ()
    go vis (RVar va) (RVar vb) = do
      (ra, a) <- repr va
      (rb, b) <- repr vb
      unless (ra == rb) $ do
        when (elem ra vis || elem rb vis) $ throwError InfiniteType
        writePoint rb (Link ra)
        r <- unify1 (\p q -> p <$ go (ra : vis) p q) a b
        writePoint ra (Rep r)
