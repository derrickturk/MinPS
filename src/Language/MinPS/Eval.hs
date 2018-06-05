{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Eval (
    RecEnv
  , emptyRecEnv
  , Eval
  , runEval
  , evalEval
  , execEval
  , eval
  , eval'
) where

import Control.Monad.State
import qualified Data.Sequence as S
import qualified Data.Text as T

import Language.MinPS.Syntax
import Language.MinPS.Value

data RecEnv = RecEnv
  { getRecEnv :: S.Seq (T.Text, Closure, Term 'Checked)
  , nextBinding :: Int
  }

emptyRecEnv :: RecEnv
emptyRecEnv = RecEnv S.empty 0

newtype Eval a = Eval { getEval :: State RecEnv a }
  deriving (Functor, Applicative, Monad, MonadState RecEnv)

runEval :: Eval a -> RecEnv -> (a, RecEnv)
runEval = runState . getEval

evalEval :: Eval a -> RecEnv -> a
evalEval = evalState . getEval

execEval :: Eval a -> RecEnv -> RecEnv
execEval = execState . getEval

eval :: Term 'Checked -> Eval Value
eval = eval' []

eval' :: Closure -> Term 'Checked -> Eval Value
eval' c (Let ctxt t) = do
  c' <- evalContext ctxt c
  eval' c' t

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
  go _ ((MkRecBinding x) :- _) 0 = do
    env <- gets getRecEnv
    case env S.!? x of
      Just (_, c', t) -> eval' c' t
      Nothing -> error "ICE: closure & rec. env. out of sync"
  go ix (_:vs) n = go ix vs (n - 1)

evalContext :: Context 'Checked -> Closure -> Eval Closure
evalContext [] c = pure c
evalContext ((x, _, t):rest) c = do
  next <- gets nextBinding
  env <- gets getRecEnv
  let c' = MkRecBinding next :- c
      env' = env S.:|> (x, c', t)
  put $ RecEnv env' (next + 1)
  evalContext rest c'
