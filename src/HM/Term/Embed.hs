{-# LANGUAGE OverloadedStrings #-}

module HM.Term.Embed where

import HM.Term

λ :: String -> Term -> Term
λ str t = Term $ Lam str t

infixl 9 @

(@) :: Term -> Term -> Term
f @ x = Term $ App f x

let' :: String -> Term -> Term -> Term
let' name bound body = Term $ Let name bound body

pair :: Term -> Term -> Term
pair a b = Term (Pair a b)

letrec :: [(String, Term)] -> Term -> Term
letrec binds body = Term $ LetRec binds body

letrec1 :: String -> Term -> Term -> Term
letrec1 name bound body = Term $ LetRec [(name, bound)] body

unit :: Term
unit = Term Unit

var :: String -> Term
var = Term . Var

-- | generate a term for performance testing.
--
-- explode 0 = id
-- explode n = let v_n = explode (n-1) in (v_n, v_n)
--
-- This has O(n) constructors, but O(2^n) type variables
explodeLet :: Int -> Term
explodeLet n
  | n < 1 = λ "x" "x"
  | otherwise =
      let v = 'v' : show n
       in let' v (explodeLet (n - 1)) (pair (var v) (var v))
