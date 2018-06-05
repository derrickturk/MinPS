{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Eval (
    RecEnv
  , emptyRecEnv
  , Eval
  , runEval
  , eval
  , eval'
) where

import Control.Monad.Reader
import qualified Data.Map as M
import qualified Data.Text as T

import Language.MinPS.Syntax
import Language.MinPS.Value

data RecEnv = MkRecEnv { getEnv :: M.Map T.Text (Closure, Term 'Checked) }

emptyRecEnv :: RecEnv
emptyRecEnv = MkRecEnv M.empty

newtype Eval a = Eval { getEval :: Reader RecEnv a }
  deriving (Functor, Applicative, Monad, MonadReader RecEnv)

runEval :: Eval a -> RecEnv -> a
runEval = runReader . getEval

eval :: Term 'Checked -> Eval Value
eval = eval' []

eval' :: Closure -> Term 'Checked -> Eval Value
eval' c (Let ctxt t) = do
  (c', env') <- evalContext ctxt c
  pure $ runEval (eval' c' t) env'

eval' _ Type = pure VType
eval' c (Var i) = lookupVar c i
eval' c (Pi x ty t) = pure $ VPi c x ty t
eval' c (Sigma x ty t) = pure $ VSigma c x ty t
eval' c (Lam x t) = pure $ VLam c x t
eval' c (Pair t u) = pure $ VPair c t u
eval' _ (Enum lbls) = pure $ VEnum lbls
eval' _ (EnumLabel lbl) = pure $ VEnumLabel lbl
eval' c (Lift t) = pure $ VLift c t
eval' c (Box t) = pure $ VBox c t
eval' c (Rec t) = pure $ VRec c t
eval' c (Fold t) = pure $ VFold c t

eval' c (App f x) = eval' c f >>= \case
  VNeutral n -> pure $ VNeutral $ NApp n c x
  VLam c' _ body -> do
    x' <- eval' c x
    eval' (x' :+ c') body
  _ -> error "ICE: invalid application passed check"

eval' c (Split t x y u) = eval' c t >>= \case
  VNeutral n -> pure $ VNeutral $ NSplit n c x y u
  VPair c' t1 t2 -> do
    t1' <- eval' c' t1
    t2' <- eval' c' t2
    eval' (t2' :+ t1' :+ c) u
  _ -> error "ICE: invalid split passed check"

eval' c (Case t cases) = eval' c t >>= \case
  VNeutral n -> pure $ VNeutral $ NCase n c cases
  VEnumLabel l -> case lookup l cases of
    Just u -> eval' c u
    Nothing -> error "ICE: invalid case passed check"
  _ -> error "ICE: invalid case passed check"

eval' c (Force t) = eval' c t >>= \case
  VNeutral n -> pure $ VNeutral $ NForce n
  VBox c' t' -> eval' c' t'
  _ -> error "ICE: invalid force passed check"

eval' c (Unfold t x u) = eval' c t >>= \case
  VNeutral n -> pure $ VNeutral $ NUnfold n c x u
  VFold c' t' -> do
    t'' <- eval' c' t'
    eval' (t'' :+ c) u
  _ -> error "ICE: invalid unfold passed check"

lookupVar :: Closure -> Int -> Eval Value
lookupVar c i = go i c i where
  go ix [] _ = pure $ VNeutral $ NVar ix
  go _ (v :+ _) 0 = pure v
  go _ (r :- _) 0 = error "dunno yet!"
  go ix (_:vs) n = go ix vs (n - 1)

evalContext :: Context 'Checked -> Closure -> Eval (Closure, RecEnv)
evalContext [] c = ask >>= \e -> pure (c, e) -- TODO
{--
evalContext ((_, _, t):rest) c = let fixT = eval' (fixT :+ c) t in
  evalContext rest (fixT :+ c)
--}
