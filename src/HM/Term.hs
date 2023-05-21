{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HM.Term
  ( TermF (..),
    termFT,
    Term (..),
    TermInfo (..),
    Usage (..),
    Binder (..),
    FreeVars (..),
    resolve,
    alphaEquivalent,
    deBruijn,
  )
where

import Control.DeepSeq (NFData)
import Control.Monad.Trans.State
import Data.Bitraversable (bitraverse)
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (IsString (..))
import Data.Traversable (for)
import GHC.Generics
import Lib.Binder

data TermF b v a
  = Var v
  | Lam b a
  | App a a
  | Let b a a
  | LetRec [(b, a)] a
  | Lit Int
  | Unit
  | Plus a a
  | Pair a a
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic)
  deriving anyclass (NFData)

{-# INLINE termFT #-}
termFT ::
  Applicative m =>
  (b -> m b') ->
  (v -> m v') ->
  (a -> m a') ->
  (TermF b v a -> m (TermF b' v' a'))
termFT fb fv fa = go
  where
    go (Var v) = Var <$> fv v
    go (Lam b a) = Lam <$> fb b <*> fa a
    go (App a b) = App <$> fa a <*> fa b
    go (Let n b a) = Let <$> fb n <*> fa b <*> fa a
    go (LetRec bs a) = LetRec <$> traverse (bitraverse fb fa) bs <*> fa a
    go (Lit n) = pure (Lit n)
    go Unit = pure Unit
    go (Plus a b) = Plus <$> fa a <*> fa b
    go (Pair a b) = Pair <$> fa a <*> fa b

instance IsString v => IsString (TermF b v a) where
  fromString = Var . fromString

instance Num Term where
  fromInteger = Term . Lit . fromInteger
  a + b = Term (Plus a b)
  (*) = error "not implemented"
  (-) = error "not implemented"
  abs = error "not implemented"
  signum = error "not implemented"

newtype Term = Term (TermF String String Term)
  deriving newtype (Eq, Show, IsString)
  deriving stock (Generic)

data Tree a = Leaf !a | Branch !(Tree a) !(Tree a)
  deriving stock (Functor, Foldable, Traversable, Generic)
  deriving anyclass (NFData)

newtype FreeVars = FreeVars {unFreeVars :: Map String (Tree Usage)}
  deriving newtype (NFData)

instance Semigroup FreeVars where FreeVars a <> FreeVars b = FreeVars $ Map.unionWith Branch a b

instance Monoid FreeVars where mempty = FreeVars mempty

type Context = Map String Binder

insert :: Binder -> Context -> Context
insert b = Map.insert (binderName b) b

singleton :: String -> Usage -> FreeVars
singleton s v = FreeVars $ Map.singleton s (Leaf v)

delete :: String -> FreeVars -> FreeVars
delete s (FreeVars v) = FreeVars (Map.delete s v)

data TermInfo = TermInfo
  { freeVars :: FreeVars,
    infoTerm :: TermF Binder Usage TermInfo
  }
  deriving stock (Generic)
  deriving anyclass (NFData)

resolve :: Term -> TermInfo
resolve term' = evalState (go mempty 0 term') 0
  where
    tick :: State Int Int
    tick = state $ \n -> (n, n + 1)
    mkBinder :: String -> Context -> Depth -> State Int Binder
    mkBinder lbl ctx depth = do
      binderId <- tick
      pure $ BinderInfo lbl binderId depth (Map.lookup lbl ctx)
    go :: Context -> Depth -> Term -> State Int TermInfo
    go ctx depth (Term term) = case term of
      Var v -> flip fmap tick $ \varId ->
        let var = Usage v varId (Map.lookup v ctx) depth
         in TermInfo (singleton v var) $ Var var
      Lam name body -> do
        binder <- mkBinder name ctx depth
        body' <- go (insert binder ctx) (depth + 1) body
        pure $ TermInfo (delete name $ freeVars body') $ Lam binder body'
      App a b -> do
        a' <- go ctx depth a
        b' <- go ctx depth b
        pure $ TermInfo (freeVars a' <> freeVars b') $ App a' b'
      Let name def body -> do
        def' <- go ctx depth def
        binder <- mkBinder name ctx depth
        body' <- go (insert binder ctx) (depth + 1) body
        pure $
          TermInfo
            { freeVars = freeVars def' <> delete name (freeVars body'),
              infoTerm = Let binder def' body'
            }
      LetRec defs body -> do
        -- TODO check name collisions
        binders <- for (zip defs [0 ..]) $ \((binder, _), offset) ->
          mkBinder binder ctx (depth + offset)
        let ctx' = foldr insert ctx binders
            depth' = depth + length defs
        defs' <- for defs $ \(_, def) -> go ctx' depth' def
        body' <- go ctx' depth' body
        pure $
          TermInfo
            { freeVars =
                let v' = foldr ((<>) . freeVars) (freeVars body') defs'
                 in foldr (delete . binderName) v' binders,
              infoTerm = LetRec (zip binders defs') body'
            }
      Lit n -> pure $ TermInfo mempty (Lit n)
      Unit -> pure $ TermInfo mempty Unit
      Plus a b -> do
        a' <- go ctx depth a
        b' <- go ctx depth b
        pure $ TermInfo (freeVars a' <> freeVars b') (Plus a' b')
      Pair a b -> do
        a' <- go ctx depth a
        b' <- go ctx depth b
        pure $ TermInfo (freeVars a' <> freeVars b') (Pair a' b')

-- TODO ignore letrec order?
alphaEquivalent :: TermInfo -> TermInfo -> Bool
alphaEquivalent (TermInfo _ a0) (TermInfo _ b0) = goTerm a0 b0
  where
    goTerm
      (Var (Usage _ _ (Just (BinderInfo _ _ d1 _)) _))
      (Var (Usage _ _ (Just (BinderInfo _ _ d2 _)) _)) =
        d1 == d2
    goTerm
      (Var (Usage name1 _ Nothing _))
      (Var (Usage name2 _ Nothing _)) =
        name1 == name2
    goTerm (Lam _ b1) (Lam _ b2) = alphaEquivalent b1 b2
    goTerm (App a1 b1) (App a2 b2) = alphaEquivalent a1 a2 && alphaEquivalent b1 b2
    goTerm (Let _ bind1 body1) (Let _ bind2 body2) = alphaEquivalent bind1 bind2 && alphaEquivalent body1 body2
    goTerm (LetRec bind1 body1) (LetRec bind2 body2) = length bind1 == length bind2 && and (zipWith (alphaEquivalent `on` snd) bind1 bind2) && alphaEquivalent body1 body2
    goTerm (Lit a) (Lit b) = a == b
    goTerm (Plus a1 b1) (Plus a2 b2) = alphaEquivalent a1 a2 && alphaEquivalent b1 b2
    goTerm (Pair a1 b1) (Pair a2 b2) = alphaEquivalent a1 a2 && alphaEquivalent b1 b2
    goTerm Unit Unit = True
    goTerm _ _ = False

deBruijn :: Usage -> Maybe Int
deBruijn (Usage _ _ (Just (BinderInfo _ _ bind _)) use) = Just (use - bind - 1)
deBruijn _ = Nothing
