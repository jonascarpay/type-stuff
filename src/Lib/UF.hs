{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Lib.UF where

import Control.Monad.ST.Class
import Control.Monad.State.Strict
import Data.STRef

newtype Point s a = Point {unPoint :: STRef s (Link s a)}
  deriving (Eq)

data Link s a
  = Rep a
  | Link (Point s a)

{-# INLINE repr #-}
repr :: MonadST m => Point (World m) a -> m (Point (World m) a, a)
repr p =
  readPoint p >>= \case
    Rep a -> pure (p, a)
    Link p' -> do
      r <- repr p'
      writePoint p (Link (fst r))
      pure r

{-# INLINE fresh #-}
fresh :: MonadST m => a -> m (Point (World m) a)
fresh a = Point <$> liftST (newSTRef (Rep a))

{-# INLINE unify #-}
unify :: MonadST m => Point (World m) a -> Point (World m) a -> m ()
unify pa pb = do
  (ra, _) <- repr pa
  (rb, _) <- repr pb
  unless (ra == rb) $
    writePoint rb (Link ra)

{-# INLINE unifyWith #-}
unifyWith :: MonadST m => (a -> a -> m a) -> Point (World m) a -> Point (World m) a -> m ()
unifyWith f pa pb = do
  (ra, a) <- repr pa
  (rb, b) <- repr pb
  unless (ra == rb) $ do
    r <- f a b
    writePoint rb (Link ra)
    writePoint ra (Rep r)

{-# INLINE readPoint #-}
readPoint :: MonadST m => Point (World m) a -> m (Link (World m) a)
readPoint (Point p) = liftST (readSTRef p)

{-# INLINE writePoint #-}
writePoint :: MonadST m => Point (World m) a -> Link (World m) a -> m ()
writePoint (Point p) l = liftST (writeSTRef p l)

{-# INLINE capture #-}
capture ::
  forall t m b a.
  (Traversable t, MonadST m) =>
  (a -> m (Maybe b)) ->
  (t (Point (World m) a) -> m (t (Either b (Point (World m) a))))
capture f t = evalStateT (traverse go t) []
  where
    go ::
      Point (World m) a ->
      StateT
        [(Point (World m) a, Either b (Point (World m) a))]
        m
        (Either b (Point (World m) a))
    go p = do
      (rep, a) <- repr p
      gets (lookup rep) >>= \case
        Nothing -> do
          r <- maybe (Right rep) Left <$> lift (f a)
          modify ((rep, r) :)
          pure r
        Just r -> pure r

{-# INLINE captureM #-}
captureM ::
  forall m b a r.
  (MonadST m) =>
  (a -> m (Maybe b)) ->
  ( (Point (World m) a -> m (Either b (Point (World m) a))) ->
    m r
  ) ->
  m r
captureM f k = do
  ctx <- liftST (newSTRef [])
  k (mk ctx)
  where
    mk ::
      STRef (World m) [(Point (World m) a, Either b (Point (World m) a))] ->
      Point (World m) a ->
      m (Either b (Point (World m) a))
    mk ref p = do
      (rep, a) <- repr p
      ctx <- liftST (readSTRef ref)
      case lookup rep ctx of
        Nothing -> do
          r <- maybe (Right rep) Left <$> f a
          liftST $ writeSTRef ref ((rep, r) : ctx)
          pure r
        Just r -> pure r
