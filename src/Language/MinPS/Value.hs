{-# LANGUAGE GADTs, DataKinds #-}

module Language.MinPS.Value (
    Value(..)
  , Neutral(..)
) where

import Language.MinPS.Syntax
import Language.MinPS.Closure

data Value =
    VType
  | VPi Ident (Closure (CTerm, CTerm))
  | VSigma Ident (Closure (CTerm, CTerm))
  | VLam Ident (Closure (CTerm))
  | VPair (Closure (CTerm, CTerm))
  | VEnum [Label]
  | VEnumLabel Label
  | VLift (Closure (CTerm))
  | VBox (Closure (CTerm))
  | VRec (Closure (CTerm))
  | VFold (Closure (CTerm))
  | VNeutral Neutral
  deriving (Show, Eq)

data Neutral =
    NVar Int
  | NApp Neutral (Closure (CTerm))
  | NSplit Neutral Ident Ident (Closure (CTerm))
  | NCase Neutral (Closure [(Label, CTerm)])
  | NForce Neutral
  | NUnfold Neutral Ident (Closure (CTerm))
  deriving (Show, Eq)
