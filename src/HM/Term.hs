{-# LANGUAGE DeriveTraversable #-}

module HM.Term where

import Data.String (IsString)
import GHC.Exts (IsString (..))
import Rebound

data Term a
  = Var a
  | Lam (Term (Bind1 a))
  | App (Term a) (Term a)
  | Let (Term a) (Term (Bind1 a))
  | Int Int
  | Unit
  | Plus (Term a) (Term a)
  | Pair (Term a) (Term a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

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
