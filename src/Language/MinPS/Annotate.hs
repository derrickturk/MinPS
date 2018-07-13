{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE TypeFamilies, PatternSynonyms #-}

module Language.MinPS.Annotate (
    ATerm
  , Arity(..)
  , EnumRepr(..)
  , LabelRepr
  , Saturation(..)
  , annotate
  , annotate'
  , annotateStmt

  , pattern ALet
  , pattern AType
  , pattern AVar
  , pattern APi
  , pattern ASigma
  , pattern APair
  , pattern AEnum
  , pattern AEnumLabel
  , pattern ALift
  , pattern ABox
  , pattern ARec
  , pattern AFold
  , pattern ASplit
  , pattern ACase
  , pattern AForce
  , pattern AUnfold
  , pattern APolyLam
  , pattern ASatApp
) where

import Control.Monad.State
import Data.Void
import Data.List (elemIndex)
import qualified Data.Map as M

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.JS.Syntax

type ATerm = TermX 'Annotated

data Arity =
    AZ
  | AS Ident Arity
  deriving (Eq, Show)

data EnumRepr =
    VoidRepr
  | UnitRepr
  | BoolRepr
  | IntRepr
  deriving (Eq, Show)

type LabelRepr = M.Map Label JSExpr

data Saturation =
    Saturated
  | Unsaturated [Ident] [Ident]
  deriving (Eq, Show)

data Rewrite =
    PolyLam Arity ATerm -- rewrite nested lambdas to polyadic fns
  | SatApp Saturation ATerm ATerm -- rewrite nested application

-- dunno what to do with pairs yet
-- TODO: erasure annotation (e.g. Type)

type instance XLet 'Annotated = ()
type instance XType 'Annotated = ()
type instance XVar 'Annotated = Int -- de Bruijn indices; probably, eventually, do an occurs check here
type instance XPi 'Annotated = Arity
type instance XSigma 'Annotated = Arity -- let's do it and see what happens
type instance XLam 'Annotated = Void -- must be rewritted to PolyLams
type instance XPair 'Annotated = ()
type instance XEnum 'Annotated = (EnumRepr, LabelRepr)
type instance XEnumLabel 'Annotated = (EnumRepr, LabelRepr)
type instance XLift 'Annotated = ()
type instance XBox 'Annotated = ()
type instance XRec 'Annotated = ()
type instance XFold 'Annotated = ()
type instance XApp 'Annotated = Void -- these must be rewritted to SatApps
type instance XSplit 'Annotated = ()
type instance XCase 'Annotated = (EnumRepr, LabelRepr)
type instance XForce 'Annotated = ()
type instance XUnfold 'Annotated = () -- might distinguish unfold which create new bindings from those that shadow
type instance XTerm 'Annotated = Rewrite

pattern ALet :: Context 'Annotated -> ATerm -> ATerm
pattern ALet ctxt t = Let () ctxt t

pattern AType :: ATerm
pattern AType = Type ()

pattern AVar :: Int -> Ident -> ATerm
pattern AVar i x = Var i x

pattern APi :: Arity -> Ident -> ATerm -> ATerm -> ATerm
pattern APi a x ty t = Pi a x ty t

pattern ASigma :: Arity -> Ident -> ATerm -> ATerm -> ATerm
pattern ASigma a x ty t = Sigma a x ty t

pattern APair :: ATerm -> ATerm -> ATerm
pattern APair t u = Pair () t u

pattern AEnum :: EnumRepr -> LabelRepr -> [Label] -> ATerm
pattern AEnum erep lrep lbls = Enum (erep, lrep) lbls

pattern AEnumLabel :: EnumRepr -> LabelRepr -> Label -> ATerm
pattern AEnumLabel erep lrep l = EnumLabel (erep, lrep) l

pattern ALift :: ATerm -> ATerm
pattern ALift ty = Lift () ty

pattern ABox :: ATerm -> ATerm
pattern ABox t = Box () t

pattern ARec :: ATerm -> ATerm
pattern ARec ty = Rec () ty

pattern AFold :: ATerm -> ATerm
pattern AFold t = Fold () t

pattern ASplit :: ATerm -> Ident -> Ident -> ATerm -> ATerm
pattern ASplit t x y u = Split () t x y u

pattern ACase :: EnumRepr -> LabelRepr -> ATerm -> [(Label, ATerm)] -> ATerm
pattern ACase erep lrep t cases = Case (erep, lrep) t cases

pattern AForce :: ATerm -> ATerm
pattern AForce t = Force () t

pattern AUnfold :: ATerm -> Ident -> ATerm -> ATerm
pattern AUnfold t x u = Unfold () t x u

pattern APolyLam :: Arity -> ATerm -> ATerm
pattern APolyLam a t = TermX (PolyLam a t)

pattern ASatApp :: Saturation -> ATerm -> ATerm -> ATerm
pattern ASatApp s f x = TermX (SatApp s f x)

{-# COMPLETE ALet, AType, AVar, APi, ASigma,
   APair, AEnum, AEnumLabel, ALift, ABox, ARec,
   AFold, ASplit, ACase, AForce, AUnfold, APolyLam, ASatApp #-}

annotate :: MonadState Env m => KTerm -> m ATerm
annotate = annotate' []

annotate' :: MonadState Env m => [Ident] -> KTerm -> m ATerm
annotate' s (KLet _ ctxt t) = do
  (s', ctxt') <- annotateContext s ctxt
  t' <- annotate' s' t
  pure $ ALet ctxt' t'

annotate' _ (KType _) = pure AType

annotate' s (KVar _ v) = case elemIndex v s of
  Just i -> pure $ AVar i v
  _ -> error "internal error: unbound var in annotation"

-- TODO: these should probably just end up erased 
annotate' s py@(KPi _ x ty t) = do
  let arity = piArity (forget py)
  ty' <- annotate' s ty
  t' <- annotate' (x:s) t
  pure $ APi arity x ty' t'

annotate' s sig@(KSigma _ x t u) = do
  let arity = sigmaArity (forget sig)
  t' <- annotate' s t
  u' <- annotate' (x:s) u
  pure $ ASigma arity x t' u'

annotateStmt :: MonadState Env m
             => [Ident]
             -> Stmt 'KnownType
             -> m ([Ident], Stmt 'Annotated)
annotateStmt s (Declare x ty) = annotate' s ty >>= \ty' ->
  pure (x:s, Declare x ty')
annotateStmt s (Define x t) = annotate' s t >>= \t' ->
  pure (s, Define x t')
annotateStmt s (DeclareDefine x ty t) = do
  ty' <- annotate' s ty
  let s' = (x:s)
  t' <- annotate' s' t
  pure (s', DeclareDefine x ty' t')

annotateContext :: MonadState Env m
                => [Ident]
                -> Context 'KnownType
                -> m ([Ident], Context 'Annotated)
annotateContext s [] = pure (s, [])
annotateContext s (stmt:rest) = do
  (s', stmt') <- annotateStmt s stmt
  (s'', rest') <- annotateContext s' rest
  pure (s'', stmt':rest')

piArity :: CTerm -> Arity
piArity (CPi x _ r) = AS x (piArity r)
piArity _ = AZ

sigmaArity :: CTerm -> Arity
sigmaArity (CSigma x _ r) = AS x (sigmaArity r)
sigmaArity _ = AZ
