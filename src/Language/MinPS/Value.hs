{-# LANGUAGE GADTs, DataKinds #-}

module Language.MinPS.Value (
    Value(..)
  , Neutral(..)
) where

import Language.MinPS.Syntax
import Language.MinPS.Closure

data Value =
    VType
  | VPi Ident (Closure (Term 'Checked, Term 'Checked))
  | VSigma Ident (Closure (Term 'Checked, Term 'Checked))
  | VLam Ident (Closure (Term 'Checked))
  | VPair (Closure (Term 'Checked, Term 'Checked))
  | VEnum [Label]
  | VEnumLabel Label
  | VLift (Closure (Term 'Checked))
  | VBox (Closure (Term 'Checked))
  | VRec (Closure (Term 'Checked))
  | VFold (Closure (Term 'Checked))
  | VNeutral Neutral
  deriving Show

data Neutral =
    NVar Int
  | NApp Neutral (Closure (Term 'Checked))
  | NSplit Neutral Ident Ident (Closure (Term 'Checked))
  | NCase Neutral (Closure [(Label, Term 'Checked)])
  | NForce Neutral
  | NUnfold Neutral Ident (Closure (Term 'Checked))
  deriving Show
