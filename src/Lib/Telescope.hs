{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE RankNTypes #-}

module Lib.Telescope where

import Data.Proxy
import Rebound

data Telescope f g a
  = Scope (f a) (Telescope f g (Bind1 a))
  | Nil (g a)
  deriving (Functor, Foldable, Traversable)

type PTelescope = Telescope Proxy

flatten :: Telescope f (Telescope f g) a -> Telescope f g a
flatten (Scope f k) = Scope f (flatten k)
flatten (Nil g) = g
