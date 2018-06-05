{-# LANGUAGE DataKinds #-}

module Language.MinPS.Normalize (
    -- Normalize(..)
) where

import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value

class Normalize a where
  normalize :: a -> Eval (Term 'Checked)

instance Normalize Value where
  normalize VType = pure Type
  normalize (VPi c x ty t) =
    Pi x <$> (eval' c ty >>= normalize) <*> (eval' c t >>= normalize)
  {--
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
  normalize (NVar i) = pure $ Var i
  {--
  | NApp Neutral Closure (Term 'Checked)
  | NSplit Neutral Closure T.Text T.Text (Term 'Checked)
  | NCase Neutral Closure [(Label, Term 'Checked)]
  | NForce Neutral
  | NUnfold Neutral Closure T.Text (Term 'Checked)
  --}
