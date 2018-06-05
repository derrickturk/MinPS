{-# LANGUAGE DataKinds #-}

module Language.MinPS.Normalize (
    Normalize(..)
) where

import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value

class Normalize a where
  normalize' :: Closure -> a -> Eval (Term 'Checked)
  normalize :: a -> Term 'Checked
  normalize = ($ emptyRecEnv) . runEval . normalize' []

instance Normalize Value where
  normalize' _ VType = pure Type
  {--
  | VPi Closure T.Text (Term 'Checked) (Term 'Checked)
  | VSigma Closure T.Text (Term 'Checked) (Term 'Checked)
  | VLam Closure T.Text (Term 'Checked)
  | VPair Closure (Term 'Checked) (Term 'Checked)
  | VEnum [Label]
  | VEnumLabel Label
  | VLift Closure (Term 'Checked)
  | VBox Closure (Term 'Checked)
  | VRec Closure (Term 'Checked)
  | VFold Closure (Term 'Checked)
  | VNeutral Neutral
  --}

instance Normalize Neutral where
  normalize' _ (NVar i) = pure $ Var i
  {--
  | NApp Neutral Closure (Term 'Checked)
  | NSplit Neutral Closure T.Text T.Text (Term 'Checked)
  | NCase Neutral Closure [(Label, Term 'Checked)]
  | NForce Neutral
  | NUnfold Neutral Closure T.Text (Term 'Checked)
  --}
