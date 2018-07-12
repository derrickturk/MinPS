{-# LANGUAGE DataKinds, FlexibleContexts, LambdaCase #-}

module Language.MinPS.Normalize (
    Normalize(..)
) where

import Data.Fuel
import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.MinPS.Environment

import Control.Monad.State

class Normalize a where
  normalize' :: MonadState Env m => Fuel -> a -> m (CTerm)
  normalize :: MonadState Env m => a -> m (CTerm)
  normalize x = gets getFuel >>= \f -> normalize' f x

instance Normalize Value where
  normalize' _ VType = pure CType

  normalize' (More f) (VPi x ((ty, t) :@ c)) = do
    nTy <- eval' (ty :@ c) >>= normalize' f
    i <- declareE x $ Just (ty :@ c)
    nT <- eval' (t :@ (x, i):c) >>= normalize' f
    pure $ CPi x nTy nT
  normalize' Empty (VPi x ((ty, t) :@ _)) = pure $ CPi x ty t

  normalize' (More f) (VSigma x ((ty, t) :@ c)) = do
    nTy <- eval' (ty :@ c) >>= normalize' f
    i <- declareE x $ Just (ty :@ c)
    nT <- eval' (t :@ (x, i):c) >>= normalize' f
    pure $ CSigma x nTy nT
  normalize' Empty (VSigma x ((ty, t) :@ _)) = pure $ CSigma x ty t

  normalize' (More f) (VLam x (body :@ c)) = do
    i <- declareE x Nothing
    nBody <- eval' (body :@ (x, i):c) >>= normalize' f
    pure $ CLam x nBody
  normalize' Empty (VLam x (body :@ _)) = pure $ CLam x body

  normalize' (More f) (VPair ((t, u) :@ c)) = CPair
    <$> (eval' (t :@ c) >>= normalize' f)
    <*> (eval' (u :@ c) >>= normalize' f)
  normalize' Empty (VPair ((t, u) :@ _)) = pure $ CPair t u

  normalize' _ (VEnum lbls) = pure $ CEnum lbls

  normalize' _ (VEnumLabel lbl) = pure $ CEnumLabel lbl

  normalize' (More f) (VLift (t :@ c)) =
    CLift <$> (eval' (t :@ c) >>= normalize' f)
  normalize' Empty (VLift (t :@ _)) = pure $ CLift t

  -- TODO?: expand the closure (just don't eval the term!)
  -- y'know, I'm not sure their "qq" function is semantically necessary
  normalize' _ (VBox (t :@ _)) = pure $ CBox t

  normalize' (More f) (VRec (t :@ c)) =
    CRec <$> (eval' (t :@ c) >>= normalize' f)
  normalize' Empty (VRec (t :@ _)) = pure $ CRec t

  normalize' (More f) (VFold (t :@ c)) =
    CFold <$> (eval' (t :@ c) >>= normalize' f)
  normalize' Empty (VFold (t :@ _)) = pure $ CFold t

  normalize' f (VNeutral n) = normalize' f n

instance Normalize Neutral where
  normalize' _ (NVar i) = gets (lookupE i) >>= \case
    Just (EnvEntry x _ _) -> pure $ CVar x
    Nothing -> error "ICE: invalid environment index in normalization"

  normalize' (More f) (NApp n (t :@ c)) =
    CApp <$> normalize' f n <*> (eval' (t :@ c) >>= normalize' f)
  normalize' Empty (NApp n (t :@ _)) =
    CApp <$> normalize' Empty n <*> pure t

  normalize' (More f) (NSplit n x y (t :@ c)) = do
    nN <- normalize' f n
    iX <- declareE x Nothing
    iY <- declareE y Nothing
    nT <- eval' (t :@ (y, iY):(x, iX):c) >>= normalize' f
    pure $ CSplit nN x y nT
  normalize' Empty (NSplit n x y (t :@ _)) = do
    nN <- normalize' Empty n
    pure $ CSplit nN x y t

  normalize' (More f) (NCase n (cases :@ c)) =
    CCase <$> normalize' f n <*> traverse normalizeCase cases where
      normalizeCase (l, t) = do
        t' <- eval' (t :@ c) >>= normalize' f
        pure (l, t')
  normalize' Empty (NCase n (cases :@ _)) = 
    CCase <$> normalize' Empty n <*> pure cases

  normalize' f (NForce n) = CForce <$> normalize' f n

  normalize' (More f) (NUnfold n x (t :@ c)) = do
    nN <- normalize' f n
    i <- declareE x Nothing
    nT <- eval' (t :@ (x, i):c) >>= normalize
    pure $ CUnfold nN x nT
  normalize' Empty (NUnfold n x (t :@ _)) = do
    nN <- normalize' Empty n
    pure $ CUnfold nN x t
