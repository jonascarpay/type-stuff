{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Lib.UF
  ( fresh,
    Point,
    capture,
    unifyRec,
    unifyWith,
    unifyRaw,
    descriptor,
    equivalent,
  )
where

import Control.Monad.ST.Class
import Control.Monad.State.Strict
import Data.Function (on)
import Data.STRef

-- TODO assign Ints to every class to make capture and unifyRec more efficient
newtype Point s a = Point {_unPoint :: STRef s (Link s a)}
  deriving (Eq)

data Link s a
  = Rep a
  | Link (Point s a)

descriptor :: MonadST m => Point (World m) a -> m a
descriptor = fmap snd . repr

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

{-# INLINE unifyRaw #-}
unifyRaw :: MonadST m => Point (World m) a -> Point (World m) a -> m ()
unifyRaw pa pb = do
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

equivalent :: MonadST m => Point (World m) a -> Point (World m) a -> m Bool
equivalent a b = on (==) fst <$> repr a <*> repr b

-- TODO rename
{-# INLINE capture #-}
capture ::
  forall m b a r.
  MonadST m =>
  ( (Point (World m) a -> (Point (World m) a -> a -> m b) -> m b) ->
    m r
  ) ->
  m r
capture k = do
  ctx <- liftST (newSTRef [])
  k (mk ctx)
  where
    mk ::
      STRef (World m) [(Point (World m) a, b)] ->
      Point (World m) a ->
      (Point (World m) a -> a -> m b) ->
      m b
    mk ref p def = do
      (rep, a) <- repr p
      ctx <- liftST (readSTRef ref)
      case lookup rep ctx of
        Nothing -> do
          r <- def rep a
          liftST $ modifySTRef ref ((rep, r) :)
          pure r
        Just r -> pure r

unifyRec ::
  forall m a.
  (MonadST m) =>
  (forall x. m x) ->
  ( (Point (World m) a -> Point (World m) a -> m ()) ->
    (a -> a -> m a)
  ) ->
  (Point (World m) a -> Point (World m) a -> m ())
unifyRec infinite f = go []
  where
    go ::
      [Point (World m) a] ->
      Point (World m) a ->
      Point (World m) a ->
      m ()
    go vis pa pb = do
      (ra, a) <- repr pa
      (rb, b) <- repr pb
      case () of
        _
          | ra == rb -> pure ()
          | elem ra vis -> infinite
          | elem rb vis -> infinite
          | otherwise -> do
              writePoint rb (Link ra)
              r <- f (go (ra : vis)) a b
              writePoint ra (Rep r)
