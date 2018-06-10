{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Equals (
    Equals(..)
) where

import Language.MinPS.Environment
import Language.MinPS.Value
import Language.MinPS.Eval

import Control.Monad.State

class Equals a where
  (.=.) :: MonadState Env m => a -> a -> m Bool

instance Equals Value where
  x .=. y = pure False

instance Equals Neutral where
  x .=. y = pure False
