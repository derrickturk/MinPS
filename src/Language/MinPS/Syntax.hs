{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns, PatternSynonyms #-}

module Language.MinPS.Syntax (
    TermState(..)
  , Stmt(..)
  , Context
  , Label(..)
  , Ident(..)
  , TermX(..)
  , UTerm
  , CTerm
  , ReplCommand(..)

  , XLet
  , XType
  , XVar
  , XPi
  , XSigma
  , XLam
  , XPair
  , XEnum
  , XEnumLabel
  , XLift
  , XBox
  , XRec
  , XFold
  , XApp
  , XSplit
  , XCase
  , XForce
  , XUnfold
  , XTerm

  , pattern ULet
  , pattern UType
  , pattern UVar
  , pattern UPi
  , pattern USigma
  , pattern ULam
  , pattern UPair
  , pattern UEnum
  , pattern UEnumLabel
  , pattern ULift
  , pattern UBox
  , pattern URec
  , pattern UFold
  , pattern UApp
  , pattern USplit
  , pattern UCase
  , pattern UForce
  , pattern UUnfold

  , pattern CLet
  , pattern CType
  , pattern CVar
  , pattern CPi
  , pattern CSigma
  , pattern CLam
  , pattern CPair
  , pattern CEnum
  , pattern CEnumLabel
  , pattern CLift
  , pattern CBox
  , pattern CRec
  , pattern CFold
  , pattern CApp
  , pattern CSplit
  , pattern CCase
  , pattern CForce
  , pattern CUnfold
) where

import Data.Void
import Data.String
import qualified Data.Text as T

data TermState = Unchecked
               | Checked
               deriving Show

newtype Label = MkLabel { getLabel :: T.Text }
  deriving (Show, Eq, IsString, Ord)

newtype Ident = MkIdent { getIdent :: T.Text }
  deriving (Show, Eq, IsString, Ord)

data Stmt :: TermState -> * where
  Declare :: Ident -> TermX s -> Stmt s
  Define :: Ident -> TermX s -> Stmt s
  DeclareDefine :: Ident -> TermX s -> TermX s -> Stmt s

type Context s = [Stmt s]

data TermX :: TermState -> * where
  Let :: !(XLet s) -> Context s -> TermX s -> TermX s
  Type :: !(XType s) -> TermX s
  Var :: !(XVar s) -> Ident -> TermX s
  Pi :: !(XPi s) -> Ident -> TermX s -> TermX s -> TermX s
  Sigma :: !(XSigma s) -> Ident -> TermX s -> TermX s -> TermX s
  Lam :: !(XLam s) -> Ident -> TermX s -> TermX s
  Pair :: !(XPair s) -> TermX s -> TermX s -> TermX s
  Enum :: !(XEnum s) -> [Label] -> TermX s
  EnumLabel :: !(XEnumLabel s) -> Label -> TermX s
  Lift :: !(XLift s) -> TermX s -> TermX s
  Box :: !(XBox s) -> TermX s -> TermX s
  Rec :: !(XRec s) -> TermX s -> TermX s
  Fold :: !(XFold s) -> TermX s -> TermX s
  App :: !(XApp s) -> TermX s -> TermX s -> TermX s
  Split :: !(XSplit s) -> TermX s -> Ident -> Ident -> TermX s -> TermX s
  Case :: !(XCase s) -> TermX s -> [(Label, TermX s)] -> TermX s
  Force :: !(XForce s) -> TermX s -> TermX s
  Unfold :: !(XUnfold s) -> TermX s -> Ident -> TermX s -> TermX s
  TermX :: !(XTerm s) -> TermX s

data ReplCommand =
    ReplEval (TermX 'Unchecked)
  | ReplExec (Stmt 'Unchecked)
  | ReplCmd T.Text (Maybe T.Text)
  deriving (Show, Eq)

type family XLet (s :: TermState)
type family XType (s :: TermState)
type family XVar (s :: TermState)
type family XPi (s :: TermState)
type family XSigma (s :: TermState)
type family XLam (s :: TermState)
type family XPair (s :: TermState)
type family XEnum (s :: TermState)
type family XEnumLabel (s :: TermState)
type family XLift (s :: TermState)
type family XBox (s :: TermState)
type family XRec (s :: TermState)
type family XFold (s :: TermState)
type family XApp (s :: TermState)
type family XSplit (s :: TermState)
type family XCase (s :: TermState)
type family XForce (s :: TermState)
type family XUnfold (s :: TermState)
type family XTerm (s :: TermState)

type UTerm = TermX 'Unchecked
type CTerm = TermX 'Checked

type instance XLet 'Unchecked = ()
type instance XType 'Unchecked = ()
type instance XVar 'Unchecked = ()
type instance XPi 'Unchecked = ()
type instance XSigma 'Unchecked = ()
type instance XLam 'Unchecked = ()
type instance XPair 'Unchecked = ()
type instance XEnum 'Unchecked = ()
type instance XEnumLabel 'Unchecked = ()
type instance XLift 'Unchecked = ()
type instance XBox 'Unchecked = ()
type instance XRec 'Unchecked = ()
type instance XFold 'Unchecked = ()
type instance XApp 'Unchecked = ()
type instance XSplit 'Unchecked = ()
type instance XCase 'Unchecked = ()
type instance XForce 'Unchecked = ()
type instance XUnfold 'Unchecked = ()
type instance XTerm 'Unchecked = Void

-- pattern ULet :: Context 'Unchecked -> TermX 'Unchecked -> TermX 'Unchecked
pattern ULet ctxt t = Let () ctxt t
pattern UType = Type ()
pattern UVar x = Var () x
pattern UPi x ty t = Pi () x ty t
pattern USigma x ty t = Sigma () x ty t
pattern ULam x t = Lam () x t
pattern UPair t u = Pair () t u
pattern UEnum lbls = Enum () lbls
pattern UEnumLabel l = EnumLabel () l
pattern ULift ty = Lift () ty
pattern UBox t = Box () t
pattern URec ty = Rec () ty
pattern UFold t = Fold () t
pattern UApp f x = App () f x
pattern USplit t x y u = Split () t x y u
pattern UCase t cases = Case () t cases
pattern UForce t = Force () t
pattern UUnfold t x u = Unfold () t x u

type instance XLet 'Checked = ()
type instance XType 'Checked = ()
type instance XVar 'Checked = ()
type instance XPi 'Checked = ()
type instance XSigma 'Checked = ()
type instance XLam 'Checked = ()
type instance XPair 'Checked = ()
type instance XEnum 'Checked = ()
type instance XEnumLabel 'Checked = ()
type instance XLift 'Checked = ()
type instance XBox 'Checked = ()
type instance XRec 'Checked = ()
type instance XFold 'Checked = ()
type instance XApp 'Checked = ()
type instance XSplit 'Checked = ()
type instance XCase 'Checked = ()
type instance XForce 'Checked = ()
type instance XUnfold 'Checked = ()
type instance XTerm 'Checked = Void

pattern CLet ctxt t = Let () ctxt t
pattern CType = Type ()
pattern CVar x = Var () x
pattern CPi x ty t = Pi () x ty t
pattern CSigma x ty t = Sigma () x ty t
pattern CLam x t = Lam () x t
pattern CPair t u = Pair () t u
pattern CEnum lbls = Enum () lbls
pattern CEnumLabel l = EnumLabel () l
pattern CLift ty = Lift () ty
pattern CBox t = Box () t
pattern CRec ty = Rec () ty
pattern CFold t = Fold () t
pattern CApp f x = App () f x
pattern CSplit t x y u = Split () t x y u
pattern CCase t cases = Case () t cases
pattern CForce t = Force () t
pattern CUnfold t x u = Unfold () t x u

deriving instance Show (Stmt 'Checked) 
deriving instance Show (Stmt 'Unchecked) 
deriving instance Eq (Stmt 'Checked)
deriving instance Eq (Stmt 'Unchecked)

deriving instance Show (TermX 'Checked)
deriving instance Show (TermX 'Unchecked)
deriving instance Eq (TermX 'Checked)
deriving instance Eq (TermX 'Unchecked)
