{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Equals (
    Equals(..)
) where

import Language.MinPS.Environment
import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Eval

import Control.Monad.State

class Equals a where
  (.=.) :: MonadState Env m => a -> a -> m Bool
infix 3 .=.

instance Equals Value where
  VType .=. VType = pure True
  VEnum xs .=. VEnum ys = pure $ xs == ys
  VEnumLabel x .=. VEnumLabel y = pure $ x == y
  VNeutral x .=. VNeutral y = x .=. y

  VPi x ((tyX, t) :@ c) .=. VPi y ((tyY, u) :@ d) = do
    eqTy <- join $ (.=.) <$> eval' (tyX :@ c) <*> eval' (tyY :@ d)
    eqTU <- equalsBound (Just (tyX :@ c)) x (t :@ c) y (u :@ d)
    pure $ eqTy && eqTU
  _ .=. _ = pure False

equalsBound :: MonadState Env m
            => Maybe (Closure (Term 'Checked))
            -> Ident
            -> Closure (Term 'Checked)
            -> Ident
            -> Closure (Term 'Checked)
            -> m Bool
equalsBound ty x (t :@ c) y (u :@ d) = do
  iX <- declareE x ty
  vT <- eval' (t :@ (x, iX):c)
  vU <- eval' (u :@ (y, iX):d)
  vT .=. vU

instance Equals Neutral where
  NVar i .=. NVar j
    | i == j = pure True
    | otherwise = error "oh god"
  _ .=. _ = pure False
