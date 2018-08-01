{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}
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
  , Forget(..)

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

import Language.MinPS.Closure

data TermState = Unchecked
               | Checked
               | KnownType
               | Annotated
               deriving Show

newtype Label = MkLabel { getLabel :: T.Text }
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

pattern ULet :: Context 'Unchecked -> UTerm -> UTerm
pattern ULet ctxt t = Let () ctxt t

pattern UType :: UTerm
pattern UType = Type ()

pattern UVar :: Ident -> UTerm
pattern UVar x = Var () x

pattern UPi :: Ident -> UTerm -> UTerm -> UTerm
pattern UPi x ty t = Pi () x ty t

pattern USigma :: Ident -> UTerm -> UTerm -> UTerm
pattern USigma x ty t = Sigma () x ty t

pattern ULam :: Ident -> UTerm -> UTerm
pattern ULam x t = Lam () x t

pattern UPair :: UTerm -> UTerm -> UTerm
pattern UPair t u = Pair () t u

pattern UEnum :: [Label] -> UTerm
pattern UEnum lbls = Enum () lbls

pattern UEnumLabel :: Label -> UTerm
pattern UEnumLabel l = EnumLabel () l

pattern ULift :: UTerm -> UTerm
pattern ULift ty = Lift () ty

pattern UBox :: UTerm -> UTerm
pattern UBox t = Box () t

pattern URec :: UTerm -> UTerm
pattern URec ty = Rec () ty

pattern UFold :: UTerm -> UTerm
pattern UFold t = Fold () t

pattern UApp :: UTerm -> UTerm -> UTerm
pattern UApp f x = App () f x

pattern USplit :: UTerm -> Ident -> Ident -> UTerm -> UTerm
pattern USplit t x y u = Split () t x y u

pattern UCase :: UTerm -> [(Label, UTerm)] -> UTerm
pattern UCase t cases = Case () t cases

pattern UForce :: UTerm -> UTerm
pattern UForce t = Force () t

pattern UUnfold :: UTerm -> Ident -> UTerm -> UTerm
pattern UUnfold t x u = Unfold () t x u

{-# COMPLETE ULet, UType, UVar, UPi, USigma,
   ULam, UPair, UEnum, UEnumLabel, ULift, UBox, URec,
   UFold, UApp, USplit, UCase, UForce, UUnfold #-}

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

pattern CLet :: Context 'Checked -> CTerm -> CTerm
pattern CLet ctxt t = Let () ctxt t

pattern CType :: CTerm
pattern CType = Type ()

pattern CVar :: Ident -> CTerm
pattern CVar x = Var () x

pattern CPi :: Ident -> CTerm -> CTerm -> CTerm
pattern CPi x ty t = Pi () x ty t

pattern CSigma :: Ident -> CTerm -> CTerm -> CTerm
pattern CSigma x ty t = Sigma () x ty t

pattern CLam :: Ident -> CTerm -> CTerm
pattern CLam x t = Lam () x t

pattern CPair :: CTerm -> CTerm -> CTerm
pattern CPair t u = Pair () t u

pattern CEnum :: [Label] -> CTerm
pattern CEnum lbls = Enum () lbls

pattern CEnumLabel :: Label -> CTerm
pattern CEnumLabel l = EnumLabel () l

pattern CLift :: CTerm -> CTerm
pattern CLift ty = Lift () ty

pattern CBox :: CTerm -> CTerm
pattern CBox t = Box () t

pattern CRec :: CTerm -> CTerm
pattern CRec ty = Rec () ty

pattern CFold :: CTerm -> CTerm
pattern CFold t = Fold () t

pattern CApp :: CTerm -> CTerm -> CTerm
pattern CApp f x = App () f x

pattern CSplit :: CTerm -> Ident -> Ident -> CTerm -> CTerm
pattern CSplit t x y u = Split () t x y u

pattern CCase :: CTerm -> [(Label, CTerm)] -> CTerm
pattern CCase t cases = Case () t cases

pattern CForce :: CTerm -> CTerm
pattern CForce t = Force () t

pattern CUnfold :: CTerm -> Ident -> CTerm -> CTerm
pattern CUnfold t x u = Unfold () t x u

{-# COMPLETE CLet, CType, CVar, CPi, CSigma,
   CLam, CPair, CEnum, CEnumLabel, CLift, CBox, CRec,
   CFold, CApp, CSplit, CCase, CForce, CUnfold #-}

deriving instance Show (TermX 'Checked)
deriving instance Show (TermX 'Unchecked)
deriving instance Eq (TermX 'Checked)
deriving instance Eq (TermX 'Unchecked)

deriving instance Show (Stmt 'Checked) 
deriving instance Show (Stmt 'Unchecked) 
deriving instance Eq (Stmt 'Checked)
deriving instance Eq (Stmt 'Unchecked)

class Forget (f :: TermState -> *) (s :: TermState) (t :: TermState) where
  forget :: f s -> f t

-- TODO: this instance lets you forget an Unchecked to a Checked

instance (
    XTerm s ~ Void
  , XLet t ~ ()
  , XType t ~ ()
  , XVar t ~ ()
  , XPi t ~ ()
  , XSigma t ~ ()
  , XLam t ~ ()
  , XPair t ~ ()
  , XEnum t ~ ()
  , XEnumLabel t ~ ()
  , XLift t ~ ()
  , XBox t ~ ()
  , XRec t ~ ()
  , XFold t ~ ()
  , XApp t ~ ()
  , XSplit t ~ ()
  , XCase t ~ ()
  , XForce t ~ ()
  , XUnfold t ~ ()
  ) => Forget TermX s t where
  forget (Let _ ctxt t) = Let () (forget <$> ctxt) (forget t)
  forget (Type _) = Type ()
  forget (Var _ x) = Var () x
  forget (Pi _ x ty t) = Pi () x (forget ty) (forget t)
  forget (Sigma _ x ty t) = Sigma () x (forget ty) (forget t)
  forget (Lam _ x t) = Lam () x (forget t)
  forget (Pair _ x y) = Pair () (forget x) (forget y)
  forget (Enum _ lbls) = Enum () lbls
  forget (EnumLabel _ l) = EnumLabel () l
  forget (Lift _ t) = Lift () (forget t)
  forget (Box _ t) = Box () (forget t)
  forget (Rec _ t) = Rec () (forget t)
  forget (Fold _ t) = Fold () (forget t)
  forget (App _ f t) = App () (forget f) (forget t)
  forget (Split _ t x y u) = Split () (forget t) x y (forget u)
  forget (Case _ t cases) = Case () (forget t) (forgetCase <$> cases) where
    forgetCase (l, u) = (l, forget u)
  forget (Force _ t) = Force () (forget t)
  forget (Unfold _ t x u) = Unfold () (forget t) x (forget u)
  forget (TermX v) = absurd v

{- requires UndecidableInstances; I don't see the problem -}
instance Forget TermX s t => Forget Stmt s t where
  forget (Declare x ty) = Declare x (forget ty)
  forget (Define x t) = Define x (forget t)
  forget (DeclareDefine x ty t) = DeclareDefine x (forget ty) (forget t)
