{-# LANGUAGE DataKinds, FlexibleContexts #-}

module Language.MinPS.Normalize (
    Normalize(..)
) where

import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.MinPS.Environment

import Control.Monad.State

class Normalize a where
  normalize :: MonadState Env m => a -> m (Term 'Checked)

instance Normalize Value where
  normalize VType = pure Type

  normalize (VPi x ((ty, t) :@ c)) = do
    nTy <- eval' (ty :@ c) >>= normalize
    i <- declareE $ Just (ty :@ c)
    nT <- eval' (t :@ (x, i):c) >>= normalize
    pure $ Pi x nTy nT

  normalize (VSigma x ((ty, t) :@ c)) = do
    nTy <- eval' (ty :@ c) >>= normalize
    i <- declareE $ Just (ty :@ c)
    nT <- eval' (t :@ (x, i):c) >>= normalize
    pure $ Sigma x nTy nT

  normalize (VLam x (body :@ c)) = do
    i <- declareE Nothing
    nBody <- eval' (body :@ (x, i):c) >>= normalize
    pure $ Lam x nBody

  normalize (VPair ((t, u) :@ c)) = Pair
    <$> (eval' (t :@ c) >>= normalize)
    <*> (eval' (u :@ c) >>= normalize)

  normalize (VEnum lbls) = pure $ Enum lbls

  normalize (VEnumLabel lbl) = pure $ EnumLabel lbl

  -- TODO: check recursion carefully!
  normalize (VLift (t :@ c)) = Lift <$> (eval' (t :@ c) >>= normalize)

  normalize (VBox (t :@ c)) = Box <$> (eval' (t :@ c) >>= normalize)

  normalize (VRec (t :@ c)) = Rec <$> (eval' (t :@ c) >>= normalize)

  normalize (VFold (t :@ c)) = Fold <$> (eval' (t :@ c) >>= normalize)

  normalize (VNeutral n) = normalize n

instance Normalize Neutral where
  normalize (NVar i) = pure $ Var i

  normalize (NApp n (t :@ c)) =
    App <$> normalize n <*> (eval' (t :@ c) >>= normalize)

  normalize (NSplit n x y (t :@ c)) = do
    nN <- normalize n
    iX <- declareE Nothing
    iY <- declareE Nothing
    nT <- eval' (t :@ (y, iY):(x, iX):c) >>= normalize
    pure $ Split nN x y nT

  normalize (NCase n (cases :@ c)) =
    Case <$> normalize n <*> traverse normalizeCase cases where
      normalizeCase (l, t) = do
        t' <- eval' (t :@ c) >>= normalize
        pure (l, t')

  normalize (NForce n) = Force <$> normalize n

  normalize (NUnfold n x (t :@ c)) = do
    nN <- normalize n
    i <- declareE Nothing
    nT <- eval' (t :@ (x, i):c) >>= normalize
    pure $ Unfold nN x nT
