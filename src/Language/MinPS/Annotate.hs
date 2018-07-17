{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE LambdaCase, TypeFamilies, PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Language.MinPS.Annotate (
    ATerm
  , Arity(..)
  , EnumRepr
  , LabelRepr(..)
  , LabelMap
  , PairRepr(..)
  , Saturation(..)
  , Erasure(..)
  , ErasureKind(..)
  , annotate
  , annotate'
  , annotateStmt
  , annotateContext
  , annotateProgram
  , nonNullLabel

  , pattern ALet
  , pattern AVar
  , pattern APair
  , pattern AEnumLabel
  , pattern ABox
  , pattern AFold
  , pattern ASplit
  , pattern ACase
  , pattern AForce
  , pattern AUnfold
  , pattern APolyLam
  , pattern ASatApp
  , pattern AErased
) where

import Control.Monad.State
import Data.Void
import Data.List (elemIndex, sort)
import qualified Data.Map.Strict as M

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.JS.Syntax

type ATerm = TermX 'Annotated

data Arity =
    AZ
  | AS Ident Erasure Arity
  deriving (Eq, Show)

data LabelRepr =
    VoidRepr
  | UnitRepr
  | BoolRepr
  | IntRepr
  deriving (Eq, Show)

type LabelMap = M.Map Label JSExpr

type EnumRepr = (LabelRepr, LabelMap)

data PairRepr =
    PairRepr
  | NullableRepr Label EnumRepr
  deriving (Eq, Show)

data Saturation =
    Saturated
  | Unsaturated [(Erasure, Ident)]
  deriving (Eq, Show)

data Erasure =
    EKeep
  | EErase ErasureKind
  deriving (Eq, Show)

data ErasureKind =
    EKPiType Erasure
  | EKNonPiType
  | EKTypeType
  deriving (Eq, Show)

data Rewrite =
    PolyLam Arity ATerm -- rewrite nested lambdas to polyadic fns
  | SatApp Saturation ATerm [(Erasure, ATerm)] -- rewrite nested application
  | Erased ErasureKind -- an erased term
  deriving (Eq, Show)

type instance XLet 'Annotated = ()
type instance XType 'Annotated = Void -- should be erased
type instance XVar 'Annotated = Int -- de Bruijn indices; probably, eventually, do an occurs check here
type instance XPi 'Annotated = Void
type instance XSigma 'Annotated = Void -- let's do it and see what happens
type instance XLam 'Annotated = Void -- must be rewritten to PolyLams
type instance XPair 'Annotated = PairRepr
type instance XEnum 'Annotated = Void
type instance XEnumLabel 'Annotated = EnumRepr
type instance XLift 'Annotated = Void -- should be erased
type instance XBox 'Annotated = ()
type instance XRec 'Annotated = Void -- should be erased
type instance XFold 'Annotated = ()
type instance XApp 'Annotated = Void -- these must be rewritten to SatApps
type instance XSplit 'Annotated = PairRepr
type instance XCase 'Annotated = EnumRepr
type instance XForce 'Annotated = ()
type instance XUnfold 'Annotated = () -- might distinguish unfold which create new bindings from those that shadow
type instance XTerm 'Annotated = Rewrite

pattern ALet :: Context 'Annotated -> ATerm -> ATerm
pattern ALet ctxt t = Let () ctxt t

pattern AVar :: Int -> Ident -> ATerm
pattern AVar i x = Var i x

pattern APair :: PairRepr -> ATerm -> ATerm -> ATerm
pattern APair r t u = Pair r t u

pattern AEnumLabel :: EnumRepr -> Label -> ATerm
pattern AEnumLabel erep l = EnumLabel erep l

pattern ABox :: ATerm -> ATerm
pattern ABox t = Box () t

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

pattern APolyLam :: Arity -> ATerm -> ATerm
pattern APolyLam a t = TermX (PolyLam a t)

pattern ASatApp :: Saturation -> ATerm -> [(Erasure, ATerm)] -> ATerm
pattern ASatApp s f xs = TermX (SatApp s f xs)

pattern AErased :: ErasureKind -> ATerm
pattern AErased e = TermX (Erased e)

{-# COMPLETE ALet, AVar, APair, AEnumLabel, ABox, AFold, ASplit,
             ACase, AForce, AUnfold, APolyLam, ASatApp, AErased #-}

annotate :: MonadState Env m => KTerm -> m ATerm
annotate = annotate' []

annotate' :: MonadState Env m => [Ident] -> KTerm -> m ATerm
annotate' _ (KType _) = pure $ AErased EKTypeType
annotate' _ pi@(KPi _ _ _ _) =
  pure $ AErased $ EKPiType $ piShouldErase (forget pi)
annotate' _ (KSigma _ _ _ _) = pure $ AErased EKNonPiType
annotate' _ (KEnum _ _) = pure $ AErased EKNonPiType
annotate' _ (KLift _ _) = pure $ AErased EKNonPiType
annotate' _ (KRec _ _) = pure  $ AErased EKNonPiType

annotate' s (KLet _ ctxt t) = do
  (s', ctxt') <- annotateContext s ctxt
  t' <- annotate' s' t
  pure $ ALet ctxt' t'

annotate' s (KVar _ v) = case elemIndex v s of
  Just i -> pure $ AVar i v
  _ -> error "internal error: unbound var in annotation"

annotate' s lam@(KLam ty _ _) = eval' ty >>= \case
  VPi x ((ty, t) :@ _) -> case piShouldErase (CPi x ty t) of
    EErase e -> pure $ AErased e -- a bit of a lie
    EKeep -> foldLam s lam >>= \(a, body) -> pure (APolyLam a body)
  _ -> error $ "internal error: non-pi-type lambda"

annotate' s (KPair ty t u) = do
  ty' <- eval' ty
  repr <- case ty' of
    VSigma x ((ty, t) :@ c) -> pairRepr (CSigma x ty t :@ c)
    _ -> pure PairRepr
  APair repr <$> annotate' s t <*> annotate' s u

-- TODO: raw, eval, or normalize here?
annotate' _ (KEnumLabel ty l) = eval' ty >>= \case
  VEnum lbls -> pure $ AEnumLabel (enumRepr lbls) l
  _ -> error $ "internal error: expected enum type (annotating label)"

annotate' s (KBox _ t) = ABox <$> annotate' s t
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

piArity :: MonadState Env m => Closure CTerm -> m Arity
piArity (CPi x ty t :@ c) = do
  ty' <- eval' (ty :@ c)
  i <- declareE x $ Just (ty :@ c)
  a <- piArity (t :@ (x, i):c)
  pure $ AS x (typeShouldEraseV ty') a
piArity _ = pure AZ

piShouldErase :: CTerm -> Erasure
piShouldErase CType = EErase EKTypeType
piShouldErase (CPi _ _ t) = piShouldErase t
piShouldErase _ = EKeep

{-
sigmaArity :: CTerm -> Arity
sigmaArity (CSigma x _ r) = AS x (sigmaArity r)
sigmaArity _ = AZ
-}

typeShouldErase :: CTerm -> Erasure
typeShouldErase CType = EErase EKTypeType
typeShouldErase pi@(CPi _ _ _) = piShouldErase pi
typeShouldErase (CLift _) = EErase EKTypeType -- TODO: a lie
typeShouldErase _ = EKeep

typeShouldEraseV :: Value -> Erasure
typeShouldEraseV VType = EErase EKTypeType
typeShouldEraseV (VPi x ((ty, t) :@ _)) = piShouldErase (CPi x ty t)
typeShouldEraseV (VLift _) = EErase EKTypeType
typeShouldEraseV _ = EKeep

pairRepr :: MonadState Env m => Closure CTerm -> m PairRepr
pairRepr (CSigma x ty r :@ c) = eval' (ty :@ c) >>= \case
  VEnum lbls@[_, _] -> case r of
    CCase (CVar y) [(l1, r1), (l2, r2)] | x == y -> do
      i <- declareE x (Just (ty :@ c))
      r1' <- eval' (r1 :@ (x, i):c)
      r2' <- eval' (r2 :@ (x, i):c)
      case (r1', r2') of
        (VEnum [_], _) -> pure $ NullableRepr l1 (enumRepr lbls)
        (_, VEnum [_]) -> pure $ NullableRepr l2 (enumRepr lbls)
        _ -> pure PairRepr
    CForce (CCase (CVar y) [(l1, CBox r1), (l2, CBox r2)]) | x == y -> do
      i <- declareE x (Just (ty :@ c))
      r1' <- eval' (r1 :@ (x, i):c)
      r2' <- eval' (r2 :@ (x, i):c)
      case (r1', r2') of
        (VEnum [_], _) -> pure $ NullableRepr l1 (enumRepr lbls)
        (_, VEnum [_]) -> pure $ NullableRepr l2 (enumRepr lbls)
        _ -> pure PairRepr
    _ -> pure PairRepr
  _ -> pure PairRepr
pairRepr _ = pure PairRepr

foldLam :: MonadState Env m => [Ident] -> KTerm -> m (Arity, ATerm)
foldLam s (KLam ty x body) = do
  ty' <- eval' ty
  case ty' of
    VPi _ ((ty, _) :@ _) -> do
      (a, result) <- foldLam (x:s) body
      pure (AS x (typeShouldErase ty) a, result)
    _ -> error "internal error: non-pi-type lambda"
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
  satArity <- piArity (typeOf $ outerPi t)
  go satArity t u [] []
  where
    outerPi (KApp _ f _) = outerPi f
    outerPi f = f

    go (AS _ e a) (KApp _ f x) y xs es = go a f x (y:xs) (e:es)

    go (AS _ e AZ) f x xs es = ASatApp Saturated
      <$> annotate' s f
      <*> traverse (annotE s) (zip (reverse $ e:es) (x:xs))

    go (AS _ e rest) f x xs es = ASatApp (Unsaturated (names rest))
      <$> annotate' s f
      <*> traverse (annotE s) (zip (reverse $ e:es) (x:xs))

    go AZ _ _ _ _ = error "internal error: zero-arity function application"

    annotE s (e, t) = (,) <$> pure e <*> annotate' s t

    names AZ = []
    names (AS n e a) = (e, n):(names a)

-- YES I KNOW THEY'RE ORPHANS
deriving instance Show (TermX 'Annotated)
deriving instance Eq (TermX 'Annotated)

deriving instance Show (Stmt 'Annotated)
deriving instance Eq (Stmt 'Annotated)
