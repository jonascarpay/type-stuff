{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}

module Lib.Telescope where

import Control.Monad.State
import Data.Map (Map)
import Data.Proxy
import Data.Void
import Lib.Bind

data Telescope f g a
  = Scope (f a) (Telescope f g (Bind1 a))
  | Nil (g a)
  deriving (Functor, Foldable, Traversable)

type PTelescope = Telescope Proxy

flatten :: Telescope f (Telescope f g) a -> Telescope f g a
flatten (Scope f k) = Scope f (flatten k)
flatten (Nil g) = g

-- run :: (forall k. Fresh k a (f a)) -> Telescope Proxy f a
-- run _ = undefined

captureMany :: f (Either Int a) -> Telescope Proxy f a
captureMany = undefined
  where
    go :: (a -> r) -> (forall g. g r -> Telescope Proxy g a) -> Map Int r -> f r -> ()
    go _ _ _ = undefined
