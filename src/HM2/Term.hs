{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module HM2.Term
  ( TermF (..),
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

import Control.Monad.Trans.State
import Data.Function (on)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.String (IsString (..))
import Data.Traversable (for)
import GHC.Generics

data TermF b v a
  = Var v
  | Lam b a
  | App a a
  | Let b a a
  | LetRec [(b, a)] a
  deriving stock (Eq, Show, Functor, Foldable, Traversable, Generic)

instance IsString v => IsString (TermF b v a) where
  fromString = Var . fromString

newtype Term = Term (TermF String String Term)
  deriving newtype (Eq, Show, IsString)
  deriving stock (Generic)

data Tree a = Leaf !a | Branch !(Tree a) !(Tree a)
  deriving (Functor, Foldable, Traversable)

newtype FreeVars = FreeVars {unFreeVars :: Map String (Tree Usage)}

instance Semigroup FreeVars where FreeVars a <> FreeVars b = FreeVars $ Map.unionWith Branch a b

type Context = Map String Binder

insert :: Binder -> Context -> Context
insert b = Map.insert (binderName b) b

singleton :: String -> Usage -> FreeVars
singleton s v = FreeVars $ Map.singleton s (Leaf v)

delete :: String -> FreeVars -> FreeVars
delete s (FreeVars v) = FreeVars (Map.delete s v)

type Depth = Int

data TermInfo = TermInfo
  { freeVars :: FreeVars,
    infoTerm :: TermF Binder Usage TermInfo
  }

data Binder = BinderInfo
  { binderName :: !String,
    binderID :: !Int,
    binderDepth :: !Depth,
    binderShadow :: !(Maybe Binder)
  }

data Usage = Usage
  { varName :: !String,
    varID :: !Int,
    varBinder :: Maybe Binder,
    varDepth :: Depth
  }

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

-- TODO ignore letrec order?
alphaEquivalent :: TermInfo -> TermInfo -> Bool
alphaEquivalent (TermInfo _ a) (TermInfo _ b) = goTerm a b
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
    goTerm _ _ = False

deBruijn :: Usage -> Maybe Int
deBruijn (Usage _ _ (Just (BinderInfo _ _ bind _)) use) = Just (use - bind - 1)
deBruijn _ = Nothing

instance Eq Binder where (==) = on (==) binderID

instance Ord Binder where compare = on compare binderID
