{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts, UndecidableInstances #-}
{-# LANGUAGE PolyKinds, RankNTypes, BangPatterns, PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}

module Language.MinPS.Syntax (
    TermState(..)
  , Stmt(..)
  , Context
  , Label(..)
  , Ident(..)
  , TermX(..)
  , UTerm
  , CTerm
  , KTerm
  , ReplCommand(..)
  , Forget(..)
  , typeOf

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

  , pattern KLet
  , pattern KType
  , pattern KVar
  , pattern KPi
  , pattern KSigma
  , pattern KLam
  , pattern KPair
  , pattern KEnum
  , pattern KEnumLabel
  , pattern KLift
  , pattern KBox
  , pattern KRec
  , pattern KFold
  , pattern KApp
  , pattern KSplit
  , pattern KCase
  , pattern KForce
  , pattern KUnfold
) where

import Data.Void
import Data.String
import qualified Data.Text as T

import Language.MinPS.Closure

data TermState = Unchecked
               | Checked
               | KnownType
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

data TermXF :: (TermState -> *) -> TermState -> * where
  LetF :: !(XLet s) -> Context s -> f s -> TermXF f s
  TypeF :: !(XType s) -> TermXF f s

newtype Fix1 (f :: (k -> *) -> k -> *) (i :: k) = In1 { out1 :: f (Fix1 f) i }

type TermX' s = Fix1 TermXF s

-- natural transformations
type f :~> g = forall a . f a -> g a
infixr 0 :~>

class Functor1 (f :: (k -> *) -> k -> *) where
  fmap1 :: (s :~> t) -> f s :~> f t

instance Functor1 TermXF where
  fmap1 f (LetF a ctxt t) = LetF a ctxt (f t) 
  fmap1 _ (TypeF a) = TypeF a

cata1 :: Functor1 f => (f s :~> s) -> Fix1 f :~> s
cata1 f = f . fmap1 (cata1 f) . out1

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
type KTerm = TermX 'KnownType

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

type instance XLet 'KnownType = Closure CTerm
type instance XType 'KnownType = Closure CTerm
type instance XVar 'KnownType = Closure CTerm
type instance XPi 'KnownType = Closure CTerm
type instance XSigma 'KnownType = Closure CTerm
type instance XLam 'KnownType = Closure CTerm
type instance XPair 'KnownType = Closure CTerm
type instance XEnum 'KnownType = Closure CTerm
type instance XEnumLabel 'KnownType = Closure CTerm
type instance XLift 'KnownType = Closure CTerm
type instance XBox 'KnownType = Closure CTerm
type instance XRec 'KnownType = Closure CTerm
type instance XFold 'KnownType = Closure CTerm
type instance XApp 'KnownType = Closure CTerm
type instance XSplit 'KnownType = Closure CTerm
type instance XCase 'KnownType = Closure CTerm
type instance XForce 'KnownType = Closure CTerm
type instance XUnfold 'KnownType = Closure CTerm
type instance XTerm 'KnownType = Void

pattern KLet :: Closure CTerm -> Context 'KnownType -> KTerm -> KTerm
pattern KLet kTy ctxt t = Let kTy ctxt t

pattern KType :: Closure CTerm -> KTerm
pattern KType kTy = Type kTy

pattern KVar :: Closure CTerm -> Ident -> KTerm
pattern KVar kTy x = Var kTy x

pattern KPi :: Closure CTerm -> Ident -> KTerm -> KTerm -> KTerm
pattern KPi kTy x ty t = Pi kTy x ty t

pattern KSigma :: Closure CTerm -> Ident -> KTerm -> KTerm -> KTerm
pattern KSigma kTy x ty t = Sigma kTy x ty t

pattern KLam :: Closure CTerm -> Ident -> KTerm -> KTerm
pattern KLam kTy x t = Lam kTy x t

pattern KPair :: Closure CTerm -> KTerm -> KTerm -> KTerm
pattern KPair kTy t u = Pair kTy t u

pattern KEnum :: Closure CTerm -> [Label] -> KTerm
pattern KEnum kTy lbls = Enum kTy lbls

pattern KEnumLabel :: Closure CTerm -> Label -> KTerm
pattern KEnumLabel kTy l = EnumLabel kTy l

pattern KLift :: Closure CTerm -> KTerm -> KTerm
pattern KLift kTy ty = Lift kTy ty

pattern KBox :: Closure CTerm -> KTerm -> KTerm
pattern KBox kTy t = Box kTy t

pattern KRec :: Closure CTerm -> KTerm -> KTerm
pattern KRec kTy ty = Rec kTy ty

pattern KFold :: Closure CTerm -> KTerm -> KTerm
pattern KFold kTy t = Fold kTy t

pattern KApp :: Closure CTerm -> KTerm -> KTerm -> KTerm
pattern KApp kTy f x = App kTy f x

pattern KSplit :: Closure CTerm -> KTerm -> Ident -> Ident -> KTerm -> KTerm
pattern KSplit kTy t x y u = Split kTy t x y u

pattern KCase :: Closure CTerm -> KTerm -> [(Label, KTerm)] -> KTerm
pattern KCase kTy t cases = Case kTy t cases

pattern KForce :: Closure CTerm -> KTerm -> KTerm
pattern KForce kTy t = Force kTy t

pattern KUnfold :: Closure CTerm -> KTerm -> Ident -> KTerm -> KTerm
pattern KUnfold kTy t x u = Unfold kTy t x u

typeOf :: KTerm -> Closure CTerm
typeOf (KLet ty _ _) = ty
typeOf (KType ty) = ty
typeOf (KVar ty _) = ty
typeOf (KPi ty _ _ _) = ty
typeOf (KSigma ty _ _ _) = ty
typeOf (KLam ty _ _) = ty
typeOf (KPair ty _ _) = ty
typeOf (KEnum ty _) = ty
typeOf (KEnumLabel ty _) = ty
typeOf (KLift ty _) = ty
typeOf (KBox ty _) = ty
typeOf (KRec ty _) = ty
typeOf (KFold ty _) = ty
typeOf (KApp ty _ _) = ty
typeOf (KSplit ty _ _ _ _) = ty
typeOf (KCase ty _ _) = ty
typeOf (KForce ty _) = ty
typeOf (KUnfold ty _ _ _) = ty
typeOf (TermX v) = absurd v

deriving instance Show (TermX 'Checked)
deriving instance Show (TermX 'Unchecked)
deriving instance Show (TermX 'KnownType)
deriving instance Eq (TermX 'Checked)
deriving instance Eq (TermX 'Unchecked)
deriving instance Eq (TermX 'KnownType)

deriving instance Show (Stmt 'Checked) 
deriving instance Show (Stmt 'Unchecked) 
deriving instance Show (Stmt 'KnownType) 
deriving instance Eq (Stmt 'Checked)
deriving instance Eq (Stmt 'Unchecked)
deriving instance Eq (Stmt 'KnownType)

class Forget (f :: TermState -> *) (s :: TermState) (t :: TermState) where
  forget :: f s -> f t

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
