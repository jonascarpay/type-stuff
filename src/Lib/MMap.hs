{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lib.MMap where

import Control.DeepSeq (NFData)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

newtype MMap k v = MMap (Map k (Set v))
  deriving newtype (NFData)

instance (Ord k, Ord v) => Semigroup (MMap k v) where
  MMap a <> MMap b = MMap (Map.unionWith (<>) a b)

instance (Ord v, Ord k) => Monoid (MMap k v) where
  mempty = empty

delete :: Ord k => k -> MMap k v -> MMap k v
delete k (MMap m) = MMap (Map.delete k m)

singleton :: k -> v -> MMap k v
singleton k v = MMap (Map.singleton k (Set.singleton v))

empty :: MMap k v
empty = MMap Map.empty
