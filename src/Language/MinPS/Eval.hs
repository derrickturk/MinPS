{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Eval (
    eval
  , eval'
  , runEval
  , runEval'
) where

import Control.Monad.State

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Value

eval :: MonadState Env m => Term 'Checked -> m Value
eval = eval' . emptyC

eval' :: MonadState Env m => Closure (Term 'Checked) -> m Value
eval' (Let ctxt t :@ c) = do
  c' <- evalContext ctxt c
  eval' (t :@ c')

eval' (Type :@ _) = pure VType

eval' (Var i :@ c) = do
  env <- get
  case lookupSE i c env of
    Just (EnvEntry (Just t) _) -> eval' t
    -- a horrible hack; we're going to rely on the typechecker to never
    --   give us "truly undefined" bindings; however, we will, in normalisation,
    --   need a way to mark variables which should "normalize to themselves";
    --   e.g. variables introduced by binders in pi or sigma types
    Just (EnvEntry Nothing _) -> pure $ VNeutral $ NVar i
    _ -> error "ICE: undefined variable passed check"

eval' (Pi x ty t :@ c) = pure $ VPi x ((ty, t) :@ c)
eval' (Sigma x ty t :@ c) = pure $ VSigma x ((ty, t) :@ c)
eval' (Lam x t :@ c) = pure $ VLam x (t :@ c)
eval' (Pair t u :@ c) = pure $ VPair ((t, u) :@ c)
eval' (Enum lbls :@ _) = pure $ VEnum lbls
eval' (EnumLabel lbl :@ _) = pure $ VEnumLabel lbl
eval' (Lift t :@ c) = pure $ VLift (t :@ c)
eval' (Box t :@ c) = pure $ VBox (t :@ c)
eval' (Rec t :@ c) = pure $ VRec (t :@ c)
eval' (Fold t :@ c) = pure $ VFold (t :@ c)

eval' (App f x :@ c) = eval' (f :@ c) >>= \case
  VNeutral n -> pure $ VNeutral $ NApp n (x :@ c)
  VLam v (body :@ c') -> do
    i <- declareE Nothing
    defineE i (x :@ c)
    eval' (body :@ (v, i):c')
  _ -> error "ICE: invalid application passed check"

eval' (Split t x y u :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> pure $ VNeutral $ NSplit n x y (u :@ c)
  VPair ((t1, t2) :@ c') -> do
    iX <- declareE Nothing
    defineE iX (t1 :@ c')
    iY <- declareE Nothing
    defineE iY (t2 :@ c')
    eval' (u :@ (y, iY):(x, iX):c)
  _ -> error "ICE: invalid split passed check"

eval' (Case t cases :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> pure $ VNeutral $ NCase n (cases :@ c)
  VEnumLabel l -> case lookup l cases of
    Just u -> eval' (u :@ c)
    Nothing -> error "ICE: invalid case passed check"
  _ -> error "ICE: invalid case passed check"

eval' (Force t :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> pure $ VNeutral $ NForce n
  VBox t' -> eval' t'
  _ -> error "ICE: invalid force passed check"

eval' (Unfold t x u :@ c) = eval' (t :@ c) >>= \case
  VNeutral n -> pure $ VNeutral $ NUnfold n x (u :@ c)
  VFold t' -> do
    i <- declareE Nothing
    defineE i t'
    eval' (u :@ (x, i):c)
  _ -> error "ICE: invalid unfold passed check"

evalContext :: MonadState Env m => Context 'Checked -> Scope -> m Scope
evalContext [] c = pure c
evalContext ((Declare x ty):rest) c = do
  i <- declareE $ Just (ty :@ c)
  evalContext rest ((x, i):c)
evalContext ((Define x t):rest) c = case lookup x c of
    Just i -> do
      defineE i (t :@ c)
      evalContext rest c
    _ -> error "ICE: define-without-declare passed check"

runEval :: Env -> Term 'Checked -> Value
runEval e t = evalState (eval t) e

runEval' :: Env -> Closure (Term 'Checked) -> Value
runEval' e t = evalState (eval' t) e
