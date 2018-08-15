{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE LambdaCase, TypeFamilies, PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Language.MinPS.Annotate (
    ATerm
  , AStmt
  , Arity(..)
  , EnumRepr
  , LabelRepr(..)
  , LabelMap
  , PairRepr(..)
  , Saturation(..)
  , Erasure(..)
  , ErasureKind(..)
  , FreeKind(..)
  , FreeVariableMap
  , BoundVariableSet
  , ValueRec(..)
  , annotate
  , annotate'
  , annotateStmt
  , annotateContext
  , annotateProgram
  , nonNullLabel
  , free

  , pattern ADeclare
  , pattern ADefine
  , pattern ADeclareDefine

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
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Check
import Language.MinPS.Value
import Language.JS.Syntax

type ATerm = TermX 'Annotated
type AStmt = StmtX 'Annotated

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

data FreeKind =
    FreeBoxed
  | FreeUnboxed
  deriving (Eq, Show)

type FreeVariableMap = M.Map Ident FreeKind
type BoundVariableSet = S.Set Ident

data ValueRec =
    FunctionalOrNone -- no special handling needed
  | DirectRec -- compile to infinite loop
  | BoxedRec -- compile to circular structure
  deriving (Eq, Show)

type instance XDeclare 'Annotated = ValueRec
type instance XDefine 'Annotated = ValueRec
type instance XDeclareDefine 'Annotated = ValueRec
type instance XStmt 'Annotated = Void

pattern ADeclare :: ValueRec -> Ident -> ATerm -> AStmt
pattern ADeclare r x ty = Declare r x ty

pattern ADefine :: ValueRec -> Ident -> ATerm -> AStmt
pattern ADefine r x t = Define r x t

pattern ADeclareDefine :: ValueRec -> Ident -> ATerm -> ATerm -> AStmt
pattern ADeclareDefine r x ty t = DeclareDefine r x ty t

{-# COMPLETE ADeclare, ADefine, ADeclareDefine #-}

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
annotate' _ (KType _ _) = pure $ AErased EKTypeType
annotate' _ pi@(KPi _ _ _ _ _) =
  pure $ AErased $ EKPiType $ piShouldErase (forget pi)
annotate' _ (KSigma _ _ _ _ _) = pure $ AErased EKNonPiType
annotate' _ (KEnum _ _ _) = pure $ AErased EKNonPiType
annotate' _ (KLift _ _ _) = pure $ AErased EKNonPiType
annotate' _ (KRec _ _ _) = pure  $ AErased EKNonPiType

annotate' s (KLet ty env ctxt t) = do
  ty' <- evalInEnv ty env
  case typeShouldEraseV ty' of
    EKeep -> do
      (s', ctxt') <- annotateContext s ctxt
      t' <- annotate' s' t
      pure $ ALet ctxt' t'
    EErase e -> pure $ AErased e

annotate' s (KVar _ _ v) = case elemIndex v s of
  Just i -> pure $ AVar i v
  _ -> error "internal error: unbound var in annotation"

annotate' s lam@(KLam ty env _ _) = evalInEnv ty env >>= \case
  VPi x ((ty, t) :@ _) -> case piShouldErase (CPi x ty t) of
    EErase e -> pure $ AErased e -- a bit of a lie
    EKeep -> foldLam s lam >>= \(a, body) -> pure (APolyLam a body)
  _ -> error $ "internal error: non-pi-type lambda"

annotate' s (KPair ty env t u) = do
  ty' <- evalInEnv ty env
  repr <- case ty' of
    VSigma x ((ty, t) :@ c) -> pairRepr (CSigma x ty t :@ c)
    _ -> pure PairRepr
  APair repr <$> annotate' s t <*> annotate' s u

-- TODO: raw, eval, or normalize here?
annotate' _ (KEnumLabel ty env l) = evalInEnv ty env >>= \case
  VEnum lbls -> pure $ AEnumLabel (enumRepr lbls) l
  _ -> error $ "internal error: expected enum type (annotating label)"

annotate' s (KBox _ _ t) = ABox <$> annotate' s t
annotate' s (KFold _ _ t) = AFold <$> annotate' s t

annotate' s (KApp _ _ f x) = foldApp s f x

annotate' s (KSplit _ _ t x y u) = do
  tTy <- uncurry evalInEnv (typeOfE t)
  repr <- case tTy of
    VSigma x ((ty, t) :@ c) -> pairRepr (CSigma x ty t :@ c)
    _ -> pure PairRepr
  ASplit repr <$> annotate' s t
              <*> pure x
              <*> pure y
              <*> annotate' (y:x:s) u

annotate' s (KCase _ _ t cases) =
  ACase (enumRepr $ fst <$> cases) <$> annotate' s t
                                   <*> traverse annotateCase cases
  where
    annotateCase (l, u) = (,) <$> pure l <*> annotate' s u

annotate' s (KForce _ _ t) = AForce <$> annotate' s t

annotate' s (KUnfold _ _ t x u) = AUnfold <$> annotate' s t
                                        <*> pure x
                                        <*> annotate' (x:s) u

annotateStmt :: MonadState Env m
             => M.Map Ident FreeVariableMap
             -> [Ident]
             -> KStmt
             -> m (M.Map Ident FreeVariableMap, [Ident], AStmt)
annotateStmt frees s (KDeclare x ty) = do
  ty' <- annotate' s ty
  -- these get fixed up in a second pass
  -- which is ugly
  pure (frees, x:s, ADeclare FunctionalOrNone x ty')

annotateStmt frees s (KDefine x t) = do
  t' <- annotate' s t
  f <- free t
  ty <- uncurry evalInEnv (typeOfE t)
  let frees' = M.insert x f frees
      selfRef = case ty of
        VPi _ _ -> FunctionalOrNone
        _ -> case freeRec x x frees' of
          Nothing -> FunctionalOrNone
          Just FreeUnboxed -> DirectRec
          Just FreeBoxed -> BoxedRec
  pure (frees', s, ADefine selfRef x t')

annotateStmt frees s (KDeclareDefine x ty t) = do
  ty' <- annotate' s ty
  let s' = (x:s)
  t' <- annotate' s' t
  f <- free t
  ty <- uncurry evalInEnv (typeOfE t)
  let frees' = M.insert x f frees
      selfRef = case ty of
        VPi _ _ -> FunctionalOrNone
        _ -> case freeRec x x frees' of
          Nothing -> FunctionalOrNone
          Just FreeUnboxed -> DirectRec
          Just FreeBoxed -> BoxedRec
  pure (frees', s', ADeclareDefine selfRef x ty' t')

annotateContext :: MonadState Env m
                => [Ident]
                -> Context 'KnownType
                -> m ([Ident], Context 'Annotated)
annotateContext s ctxt = go [] M.empty s ctxt where
  go res _ s [] = pure (s, fixup $ reverse res)
  go res frees s (stmt:rest) = do
    (frees', s', stmt') <- annotateStmt frees s stmt
    go (stmt':res) frees' s' rest

  fixup ((ADeclare _ x ty):rest) =
    (ADeclare (defnSelfRef x rest) x ty):(fixup rest)
  fixup (s:rest) = s:(fixup rest)
  fixup [] = []

  defnSelfRef x ((ADefine ref y _):_)
    | x == y = ref
  defnSelfRef x (_:rest) = defnSelfRef x rest
  defnSelfRef _ [] = error "internal error: mismatched declare/define"

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
foldLam s (KLam ty env x body) = do
  ty' <- evalInEnv ty env
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
    outerPi (KApp _ _ f _) = outerPi f
    outerPi f = f

    go (AS _ e a) (KApp _ _ f x) y xs es = go a f x (y:xs) (e:es)

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

evalInEnv :: MonadState Env m => Closure CTerm -> Env -> m Value 
evalInEnv t env = locally (put env >> eval' t)

freePromote :: FreeKind -> FreeKind -> FreeKind
freePromote _ FreeUnboxed = FreeUnboxed
freePromote FreeUnboxed _ = FreeUnboxed
freePromote FreeBoxed FreeBoxed = FreeBoxed

freeUnion :: FreeVariableMap -> FreeVariableMap -> FreeVariableMap
freeUnion = M.unionWith freePromote

freeUnions :: [FreeVariableMap] -> FreeVariableMap
freeUnions = M.unionsWith freePromote

freeBoxAll :: FreeVariableMap -> FreeVariableMap
freeBoxAll = M.map (const FreeBoxed)

free :: MonadState Env m => KTerm -> m (M.Map Ident FreeKind)
free (KLet _ _ ctxt t) = do
  (f, b) <- varsInContext ctxt
  freeT <- free t
  pure $ freeUnion f (freeT `M.withoutKeys` b)
free (KVar _ _ x) = pure $ M.singleton x FreeUnboxed
free (KLam _ _ x t) = M.delete x <$> free t
free (KPair _ _ x y) = freeBoxAll <$> (freeUnion <$> free x <*> free y)
free (KEnumLabel _ _ _) = pure M.empty
free (KBox _ _ t) = free t
free (KFold _ _ t) = free t
free (KApp ty env f x) = do
  ty' <- evalInEnv ty env
  frees <- freeUnion <$> free f <*> free x
  case ty' of
    VSigma _ _ -> pure $ freeBoxAll frees
    _ -> pure frees
free (KSplit _ _ t x y u) = freeUnion
  <$> free t
  <*> (M.withoutKeys <$> free u <*> pure (S.fromList [x, y]))
free (KCase _ _ t cases) = freeUnion
  <$> free t
  <*> (freeUnions <$> mapM free (snd <$> cases))
free (KForce _ _ t) = free t
free (KUnfold _ _ t x u) = freeUnion <$> free t <*> (M.delete x <$> free u)

-- these are a bit silly, as they just get erased immediately
free (KType _ _) = pure M.empty
free (KPi _ _ x ty t) = freeUnion <$> free ty <*> (M.delete x <$> free t)
free (KSigma _ _ x ty t) = freeUnion <$> free ty <*> (M.delete x <$> free t)
free (KEnum _ _ _) = pure M.empty
free (KLift _ _ t) = free t
free (KRec _ _ t) = free t

varsInContext :: MonadState Env m
              => [KStmt]
              -> m (FreeVariableMap, BoundVariableSet)
varsInContext = go M.empty S.empty where
  go f b [] = pure (f, b)
  go f b ((KDeclare x ty):rest) = do
    freeTy <- free ty
    go (freeUnion f (freeTy `M.withoutKeys` b)) (S.insert x b) rest
  go f b ((KDefine _ t):rest) = do
    freeT <- free t
    go (freeUnion f (freeT `M.withoutKeys` b)) b rest
  go f b ((KDeclareDefine x ty t):rest) = do
    freeTy <- free ty
    freeT <- free t
    let b' = S.insert x b
    go (freeUnion (freeUnion f (freeTy `M.withoutKeys` b))
                  (freeT `M.withoutKeys` b'))
       b'
       rest

-- is x free (recursively) in y, and how?
freeRec :: Ident -> Ident -> M.Map Ident FreeVariableMap -> Maybe FreeKind
freeRec x y freeByName = go S.empty x y freeByName where
  go seen x y freeByName = case freeByName M.!? y of
      -- if we've followed a cycle (and thus see Nothing the second time around)
      --   we're unboxed (?)
      Nothing -> Just FreeUnboxed
      Just freeInY -> case freeInY M.!? x of
        Just f -> Just f
        Nothing -> M.foldlWithKey' promote Nothing freeInY
    where
      seen' = S.insert y seen
      freeByName' = freeByName `M.withoutKeys` seen
      -- if we're unboxed anywhere, we're unboxed
      promote (Just FreeUnboxed) _ _ = Just FreeUnboxed
      -- if we're boxed, and we're looking into a boxed definition,
      --   we're still boxed
      promote (Just FreeBoxed) _ FreeBoxed = Just FreeBoxed
      -- if we're boxed, and we're looking into an unboxed definition,
      --   we're whatever we might be inside that definition
      promote (Just FreeBoxed) v FreeUnboxed = case go seen' x v freeByName' of
        Just f -> Just f
        Nothing -> Just FreeBoxed
      -- if we're nothing, and we're looking into a boxed definition,
      --   we're at worst boxed
      promote Nothing v FreeBoxed = case go seen' x v freeByName' of
        Just _ -> Just FreeBoxed
        Nothing -> Nothing
      -- if we're nothing, and we're looking into an unboxed definition,
      --   we're whatever we might be inside that definition
      promote Nothing v FreeUnboxed = case go seen' x v freeByName' of
        Just f -> Just f
        Nothing -> Nothing

-- YES I KNOW THEY'RE ORPHANS
deriving instance Show (TermX 'Annotated)
deriving instance Eq (TermX 'Annotated)

deriving instance Show (StmtX 'Annotated)
deriving instance Eq (StmtX 'Annotated)
