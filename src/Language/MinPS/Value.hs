{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}

module Language.MinPS.Value (
    Value(..)
  , Neutral(..)
) where

import qualified Data.Text as T

import Language.MinPS.Syntax
import Language.MinPS.Context

data Value =
    VType
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
  deriving Show

data Neutral =
    NVar Int
  | NApp Neutral Closure (Term 'Checked)
  | NSplit Neutral Closure T.Text T.Text (Term 'Checked)
  | NCase Neutral Closure [(Label, Term 'Checked)]
  | NForce Neutral
  | NUnfold Neutral Closure T.Text (Term 'Checked)
  deriving Show
