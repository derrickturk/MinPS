{-# LANGUAGE DataKinds #-}

module Language.MinPS.Normalize (
    Normalize(..)
) where

import Language.MinPS.Syntax
import Language.MinPS.Value

class Normalize a where
  normalize :: a -> Term 'Checked

instance Normalize Value where
  normalize VType = Type
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
  normalize (NVar i) = Var i
  {--
  | NApp Neutral Closure (Term 'Checked)
  | NSplit Neutral Closure T.Text T.Text (Term 'Checked)
  | NCase Neutral Closure [(Label, Term 'Checked)]
  | NForce Neutral
  | NUnfold Neutral Closure T.Text (Term 'Checked)
  --}
