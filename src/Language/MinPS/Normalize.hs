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
  normalize (VSigma c x ty t) =
    Sigma x <$> (eval' c ty >>= normalize) <*> (eval' c t >>= normalize)
  -- TODO: is this right?
  normalize (VLam c x body) =
    Lam x <$> (eval' (VNeutral (NVar 0) :+ c) body >>= normalize)
  normalize (VPair c t u) =
    Pair <$> (eval' c t >>= normalize) <*> (eval' c u >>= normalize)
  normalize (VEnum lbls) = pure $ Enum lbls
  normalize (VEnumLabel lbl) = pure $ EnumLabel lbl
  -- TODO: check recursion carefully!
  normalize (VLift c t) = Lift <$> (eval' c t >>= normalize)
  normalize (VBox c t) = Box <$> (eval' c t >>= normalize)
  normalize (VRec c t) = Rec <$> (eval' c t >>= normalize)
  normalize (VFold c t) = Fold <$> (eval' c t >>= normalize)
  normalize (VNeutral n) = normalize n

instance Normalize Neutral where
  normalize (NVar i) = pure $ Var i

  normalize (NApp n c t) =
    App <$> normalize n <*> (eval' c t >>= normalize)

  normalize (NSplit n c x y t) =
    Split <$> normalize n <*> pure x <*> pure y <*> (eval' c t >>= normalize)

  normalize (NCase n c cases) =
    Case <$> normalize n <*> traverse normalizeCase cases where
      normalizeCase (l, t) = do
        t' <- eval' c t >>= normalize
        pure (l, t')

  normalize (NForce n) = Force <$> normalize n

  normalize (NUnfold n c x t) =
    Unfold <$> normalize n <*> pure x <*> (eval' c t >>= normalize)
