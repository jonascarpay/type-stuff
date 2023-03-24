{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}

module HM.Type where

import Control.Applicative
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import GHC.Generics
import Lib.Free
import Lib.Match

data TypeF a
  = Arr a a
  | TPair a a
  | TInt
  | TUnit
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic1)
  deriving anyclass (Match)

type Type = Free TypeF

infixr 2 ~>

(~>) :: Type a -> Type a -> Type a
(~>) a b = Fix (Arr a b)

tup :: Type a -> Type a -> Type a
tup a b = Fix (TPair a b)

k :: r -> (r -> a) -> a
k r f = f r

subtype :: (Ord a, Eq b) => Type a -> Type b -> Bool
subtype tsub tsup = isJust $ flip runStateT mempty $ go tsub tsup
  where
    go :: (Ord a, Eq b) => Type a -> Type b -> StateT (Map a (Type b)) Maybe ()
    go (Pure a) b =
      gets (Map.lookup a) >>= \case
        Nothing -> modify (Map.insert a b)
        Just b' | b == b' -> pure ()
        _ -> empty
    go (Fix a) (Fix b) = maybe empty sequence_ $ match go a b
    go (Fix _) (Pure _) = empty

data Scheme a
  = Scheme
      Int
      (Type (Either Int a))
  deriving (Show)

-- Technically, Scheme is a Monad, and this is be return/pure
singletonScheme :: a -> Scheme a
singletonScheme tv = Scheme 0 (pure (Right tv))
