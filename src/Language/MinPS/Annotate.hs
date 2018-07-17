{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE LambdaCase, TypeFamilies, PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Language.MinPS.Annotate (
    ATerm
  , PiArity(..)
  , SigmaArity(..)
  , EnumRepr
  , LabelRepr(..)
  , LabelMap
  , PairRepr(..)
  , Saturation(..)
  , annotate
  , annotate'
  , annotateStmt
  , annotateContext
  , annotateProgram
  , nonNullLabel

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
import Data.List (elemIndex, sort)
import qualified Data.Map.Strict as M

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Normalize
import Language.MinPS.Value
import Language.JS.Syntax

type ATerm = TermX 'Annotated

data PiArity =
    AZ
  | AS Ident PiArity
  deriving (Eq, Show)

data SigmaArity =
    AFinal
  | APair Ident SigmaArity

data LabelRepr =
    VoidRepr
  | UnitRepr
  | BoolRepr
  | IntRepr
  deriving (Eq, Show)

type LabelMap = M.Map Label JSExpr

type EnumRepr = (LabelRepr, LabelMap)

data PairRepr =
    TupleRepr SigmaArity
  | NullableRepr Label EnumRepr
  deriving (Eq, Show)

data Saturation =
    Saturated
  | Unsaturated [Ident]
  deriving (Eq, Show)

data Rewrite =
    PolyLam PiArity ATerm -- rewrite nested lambdas to polyadic fns
  | SatApp Saturation ATerm [ATerm] -- rewrite nested application
  deriving (Eq, Show)

-- dunno what to do with pairs yet
-- TODO: erasure annotation (e.g. Type)

type instance XLet 'Annotated = ()
type instance XType 'Annotated = ()
type instance XVar 'Annotated = Int -- de Bruijn indices; probably, eventually, do an occurs check here
type instance XPi 'Annotated = PiArity
type instance XSigma 'Annotated = SigmaArity -- let's do it and see what happens
type instance XLam 'Annotated = Void -- must be rewritten to PolyLams
type instance XPair 'Annotated = PairRepr
type instance XEnum 'Annotated = EnumRepr
type instance XEnumLabel 'Annotated = EnumRepr
type instance XLift 'Annotated = ()
type instance XBox 'Annotated = ()
type instance XRec 'Annotated = ()
type instance XFold 'Annotated = ()
type instance XApp 'Annotated = Void -- these must be rewritten to SatApps
type instance XSplit 'Annotated = PairRepr
type instance XCase 'Annotated = EnumRepr
type instance XForce 'Annotated = ()
type instance XUnfold 'Annotated = () -- might distinguish unfold which create new bindings from those that shadow
type instance XTerm 'Annotated = Rewrite

pattern ALet :: Context 'Annotated -> ATerm -> ATerm
pattern ALet ctxt t = Let () ctxt t

pattern AType :: ATerm
pattern AType = Type ()

pattern AVar :: Int -> Ident -> ATerm
pattern AVar i x = Var i x

pattern APi :: PiArity -> Ident -> ATerm -> ATerm -> ATerm
pattern APi a x ty t = Pi a x ty t

pattern ASigma :: SigmaArity -> Ident -> ATerm -> ATerm -> ATerm
pattern ASigma a x ty t = Sigma a x ty t

pattern APair :: PairRepr -> ATerm -> ATerm -> ATerm
pattern APair r t u = Pair r t u

pattern AEnum :: EnumRepr -> [Label] -> ATerm
pattern AEnum erep lbls = Enum erep lbls

pattern AEnumLabel :: EnumRepr -> Label -> ATerm
pattern AEnumLabel erep l = EnumLabel erep l

pattern ALift :: ATerm -> ATerm
pattern ALift ty = Lift () ty

pattern ABox :: ATerm -> ATerm
pattern ABox t = Box () t

pattern ARec :: ATerm -> ATerm
pattern ARec ty = Rec () ty

pattern AFold :: ATerm -> ATerm
pattern AFold t = Fold () t

pattern ASplit :: PairRepr -> ATerm -> Ident -> Ident -> ATerm -> ATerm
pattern ASplit r t x y u = Split r t x y u

pattern ACase :: EnumRepr -> ATerm -> [(Label, ATerm)] -> ATerm
pattern ACase erep t cases = Case erep t cases

pattern AForce :: ATerm -> ATerm
pattern AForce t = Force () t

pattern AUnfold :: ATerm -> Ident -> ATerm -> ATerm
pattern AUnfold t x u = Unfold () t x u

pattern APolyLam :: PiArity -> ATerm -> ATerm
pattern APolyLam a t = TermX (PolyLam a t)

pattern ASatApp :: Saturation -> ATerm -> [ATerm] -> ATerm
pattern ASatApp s f xs = TermX (SatApp s f xs)

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

annotate' s lam@(KLam _ _ _) = foldLam s lam >>= \(a, body)
  -> pure (APolyLam a body)

annotate' s (KPair ty t u) = do
  ty' <- eval' ty
  repr <- case ty' of
    VSigma x ((ty, t) :@ c) -> pairRepr (CSigma x ty t :@ c)
    _ -> pure $ TupleRepr (APair "_")
  APair repr <$> annotate' s t <*> annotate' s u

annotate' _ (KEnum _ lbls) = pure $ AEnum (enumRepr lbls) lbls

-- TODO: raw, eval, or normalize here?
annotate' _ (KEnumLabel ty l) = eval' ty >>= \case
  VEnum lbls -> pure $ AEnumLabel (enumRepr lbls) l
  _ -> error $ "internal error: expected enum type (annotating label)"

annotate' s (KLift _ t) = ALift <$> annotate' s t
annotate' s (KBox _ t) = ABox <$> annotate' s t
annotate' s (KRec _ t) = ARec <$> annotate' s t
annotate' s (KFold _ t) = AFold <$> annotate' s t

annotate' s (KApp _ f x) = foldApp s f x

annotate' s (KSplit _ t x y u) = do
  tTy <- eval' (typeOf t)
  repr <- case tTy of
    VSigma x ((ty, t) :@ c) -> pairRepr (CSigma x ty t :@ c)
    _ -> pure PairRepr
  ASplit repr <$> annotate' s t
              <*> pure x
              <*> pure y
              <*> annotate' (y:x:s) u

annotate' s (KCase _ t cases) =
  ACase (enumRepr $ fst <$> cases) <$> annotate' s t
                                   <*> traverse annotateCase cases
  where
    annotateCase (l, u) = (,) <$> pure l <*> annotate' s u

annotate' s (KForce _ t) = AForce <$> annotate' s t

annotate' s (KUnfold _ t x u) = AUnfold <$> annotate' s t
                                        <*> pure x
                                        <*> annotate' (x:s) u

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

annotateProgram :: MonadState Env m
                => Context 'KnownType ->
                m (Context 'Annotated)
annotateProgram = (fmap snd) . annotateContext []

nonNullLabel :: EnumRepr -> Label -> Maybe Label
nonNullLabel (BoolRepr, m) null = case M.toList (M.delete null m) of
  [(l, _)] -> Just l
  _ -> Nothing
nonNullLabel _ _ = Nothing

piArity :: CTerm -> PiArity
piArity (CPi x _ r) = AS x (piArity r)
piArity _ = AZ

sigmaArity :: CTerm -> SigmaArity
sigmaArity (CSigma x _ r) = APair x (sigmaArity r)
sigmaArity _ = AFinal

pairRepr :: MonadState Env m => Closure CTerm -> m PairRepr
pairRepr sig@(CSigma x ty r :@ c) = eval' (ty :@ c) >>= \case
  VEnum lbls@[_, _] -> case r of
    CCase (CVar y) [(l1, r1), (l2, r2)] | x == y -> do
      i <- declareE x (Just (ty :@ c))
      r1' <- eval' (r1 :@ (x, i):c)
      r2' <- eval' (r2 :@ (x, i):c)
      case (r1', r2') of
        (VEnum [_], _) -> pure $ NullableRepr l1 (enumRepr lbls)
        (_, VEnum [_]) -> pure $ NullableRepr l2 (enumRepr lbls)
        _ -> pure $ TupleRepr $ sigmaArity sig
    CForce (CCase (CVar y) [(l1, CBox r1), (l2, CBox r2)]) | x == y -> do
      i <- declareE x (Just (ty :@ c))
      r1' <- eval' (r1 :@ (x, i):c)
      r2' <- eval' (r2 :@ (x, i):c)
      case (r1', r2') of
        (VEnum [_], _) -> pure $ NullableRepr l1 (enumRepr lbls)
        (_, VEnum [_]) -> pure $ NullableRepr l2 (enumRepr lbls)
        _ -> pure $ TupleRepr $ sigmaArity sig
    _ -> pure $ TupleRepr $ sigmaArity sig
  _ -> pure $ TupleRepr $ sigmaArity sig
pairRepr _ = pure $ TupleRepr (APair "_")

foldLam :: MonadState Env m => [Ident] -> KTerm -> m (PiArity, ATerm)
foldLam s (KLam _ x body) = do
  (a, result) <- foldLam (x:s) body
  pure (AS x a, result)
foldLam s t = (,) <$> pure AZ <*> annotate' s t

enumRepr :: [Label] -> EnumRepr
enumRepr = enumRepr' . sort where
  enumRepr' [] = (VoidRepr, M.empty)
  enumRepr' [unit] = (UnitRepr, M.singleton unit JSNull)
  enumRepr' [false, true] =
    (BoolRepr, M.fromList [(false, JSBool False), (true, JSBool True)])
  enumRepr' ls = (IntRepr, M.fromList (zip ls (JSInt <$> [0..])))

foldApp :: MonadState Env m => [Ident] -> KTerm -> KTerm -> m ATerm
foldApp s t u = do
  satArity <- piArity <$> outerPi t
  go satArity t u []
  where
    outerPi (KApp _ f _) = outerPi f
    outerPi f = eval' (typeOf f) >>= normalize

    go (AS _ a) (KApp _ f x) y xs = go a f x (y:xs)
    go (AS _ AZ) f x xs =
      ASatApp Saturated <$> annotate' s f
                        <*> traverse (annotate' s) (x:xs)
    go (AS _ rest) f x xs =
      ASatApp (Unsaturated (names rest)) <$> annotate' s f
                                         <*> traverse (annotate' s) (x:xs)
    go AZ _ _ _ = error "internal error: zero-arity function application"

    names AZ = []
    names (AS n a) = n:(names a)

-- YES I KNOW THEY'RE ORPHANS
deriving instance Show (TermX 'Annotated)
deriving instance Eq (TermX 'Annotated)

deriving instance Show (Stmt 'Annotated)
deriving instance Eq (Stmt 'Annotated)
