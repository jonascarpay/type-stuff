{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HM.Term where

import Control.DeepSeq (NFData)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (IsString)
import GHC.Exts (IsString (..))
import GHC.Generics
import Rebound

data Term a
  = Var a
  | Lam (Term (Bind1 a))
  | App (Term a) (Term a)
  | Let (Term a) (Term (Bind1 a))
  | LetRec [Term (Bind Int a)] (Term (Bind Int a))
  | Int Int
  | Unit
  | Plus (Term a) (Term a)
  | Pair (Term a) (Term a)
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving anyclass (NFData)

instance Num (Term a) where
  fromInteger = Int . fromInteger
  (+) = Plus
  (*) = error "not implemented"
  (-) = error "not implemented"
  signum = error "not implemented"
  abs = error "not implemented"

instance IsString a => IsString (Term a) where
  fromString = Var . fromString

lam, λ :: Eq a => a -> Term a -> Term a
lam a = Lam . abstract1 a
λ = lam

infixl 9 @

(@) :: Term a -> Term a -> Term a
(@) = App

let' :: Eq a => a -> Term a -> Term a -> Term a
let' name bound body = Let bound (abstract1 name body)

letrec :: forall a. Ord a => [(a, Term a)] -> Term a -> Term a
letrec bindings body = LetRec (cap <$> terms) (cap body)
  where
    (names, terms) = unzip bindings
    cap :: Term a -> Term (Bind Int a)
    cap = abstract (flip Map.lookup indices)
    indices :: Map a Int
    indices = Map.fromList $ zip names [0 ..]

letrec1 :: Ord a => a -> Term a -> Term a -> Term a
letrec1 name binding = letrec [(name, binding)]

-- | generate a large term for performance testing.
-- explode 0 = id
-- explode n = (explode n-1, explode n-1)
explode :: Int -> Term a
explode = Let (Lam $ Var Bound1) . go
  where
    go :: Int -> Term (Bind1 a)
    go 0 = Var Bound1
    go n = Let (Pair (Var Bound1) (Var Bound1)) (go (n - 1))
