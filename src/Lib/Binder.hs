{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

module Lib.Binder where

import Control.DeepSeq (NFData)
import Data.Function (on)
import GHC.Generics (Generic)

type Depth = Int

data Binder = Binder
  { binderName :: !String,
    binderID :: !Int, -- Expected to be unique
    binderDepth :: !Depth,
    binderShadow :: !(Maybe Binder)
  }
  deriving stock (Generic)
  deriving anyclass (NFData)

instance Eq Binder where (==) = on (==) binderID

instance Ord Binder where compare = on compare binderID

data Usage = Usage
  { varName :: !String,
    varID :: !Int, -- Expected to be unique
    varBinder :: Maybe Binder, -- If this is `Just b`, that binderName b == varName v
    varDepth :: Depth
  }
  deriving stock (Generic)
  deriving anyclass (NFData)

instance Eq Usage where (==) = on (==) varID

instance Ord Usage where compare = on compare varID
