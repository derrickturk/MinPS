{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MinPS.Value (
    RecBinding(..)
  , Closure
  , pattern (:+)
  , pattern (:-)
  , Value(..)
  , Neutral(..)
) where

import qualified Data.Text as T

import Language.MinPS.Syntax

newtype RecBinding = MkRecBinding { recBoundName :: T.Text }
  deriving Show

type Closure = [Either RecBinding Value]

pattern (:+) :: Value -> Closure -> Closure
pattern x :+ xs = (Right x) : xs
infixr 5 :+

pattern (:-) :: RecBinding -> Closure -> Closure
pattern x :- xs = (Left x) : xs
infixr 5 :-

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
