{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances, PatternSynonyms, TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Check (
    TypeError(..)
  , KTerm
  , check
  , check'
  , checkStmt
  , checkContext
  , checkProgram
  , infer
  , runCheck
  , runCheck'
  , runInfer
  , typeOf
  , typeOfE

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

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Normalize

import Data.Void
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as Set

data TypeError =
    Mismatch (CTerm) (CTerm)
  | ExpectedGotLambda (CTerm)
  | ExpectedGotPair (CTerm)
  | ExpectedGotLabel Label (CTerm)
  | ExpectedPiType (CTerm)
  | ExpectedSigmaType (CTerm)
  | ExpectedEnumType (CTerm)
  | ExpectedLiftedType (CTerm)
  | ExpectedRecType (CTerm)
  | Undeclared Ident
  | Undefined Ident
  | DuplicateDeclare Ident
  | DuplicateDefine Ident
  | DuplicateLabel Label
  | LabelsMismatch [Label] [Label]
  | NotInferable (Closure (UTerm))
  deriving Show

type KTerm = TermX 'KnownType

check :: (MonadState Env m, MonadError TypeError m)
      => UTerm
      -> Closure (CTerm)
      -> m (KTerm)
check t = check' $ emptyC t

check' :: (MonadState Env m, MonadError TypeError m)
       => Closure (UTerm)
       -> Closure (CTerm)
       -> m (KTerm)

-- as in the original, we "first handle the cases that may potentially
-- change the environment". I am not 100% sure this split is necessary.
check' (ULet ctxt t :@ c) ty = do
  (ctxt' :@ c') <- checkContext (ctxt :@ c)
  t' <- check' (t :@ c') ty
  kLet ty ctxt' t'

check' (USplit t x y u :@ c) ty
  | x == y = throwError $ DuplicateDeclare y
  | otherwise = do
      t' <- infer (t :@ c)
      tyV <- eval' (typeOf t')
      case tyV of
        VSigma z ((a, b) :@ d) -> do
          tV <- eval' (forget t' :@ c)
          i <- declareE x (Just (a :@ d))
          j <- declareE y (Just (b :@ (z, i):d))
          let c' = (y, j):(x, i):c
          u' <- case tV of
            VNeutral (NVar k) -> locally $ do
              defineE k (CPair (CVar x) (CVar y) :@ c')
              check' (u :@ c') ty
            _ -> check' (u :@ c') ty
          kSplit ty t' x y u'
        _ -> throwError =<< ExpectedSigmaType <$> normalize tyV

check' (UCase t cases :@ c) ty = do
  t' <- infer (t :@ c)
  tyV <- eval' (typeOf t')
  case tyV of
    VEnum lbls -> let lbls' = fmap fst cases in
      if Set.fromList lbls /= Set.fromList lbls'
        then throwError $ LabelsMismatch lbls' lbls
        else do
          cases' <- mapM checkCase cases
          kCase ty t' (zip lbls' cases')
          where
            checkCase (l, u) = withConstraint
              (forget t' :@ c) l (check' (u :@ c) ty)
    _ -> throwError =<< ExpectedEnumType <$> normalize tyV

check' (UForce t :@ c) (ty :@ d) = do
  t' <- check' (t :@ c) (CLift ty :@ d)
  kForce (ty :@ d) t'

check' (UUnfold t x u :@ c) ty = do
  t' <- infer (t :@ c)
  tyV <- eval' (typeOf t')
  case tyV of
    VRec (a :@ d) -> do
      tV <- eval' (forget t' :@ c)
      i <- declareE x (Just (CForce a :@ d))
      let c' = (x, i):c
      u' <- case tV of
        VNeutral (NVar k) -> locally $ do
          defineE k (CFold (CVar x) :@ c')
          check' (u :@ c') ty
        _ -> check' (u :@ c') ty
      kUnfold ty t' x u'
    _ -> throwError =<< ExpectedRecType <$> normalize tyV

-- the default case
check' t ty = do
  eval' ty >>= checkValue t

checkValue :: (MonadState Env m, MonadError TypeError m)
           => Closure (UTerm)
           -> Value
           -> m (KTerm)

-- some cases can't be inferred...
checkValue (ULam x t :@ c) (VPi y ((ty, u) :@ d)) = do
  i <- declareE x (Just (ty :@ d))
  t' <- check' (t :@ (x, i):c) (u :@ (y, i):d)
  kLam (CPi y ty u :@ d) x t'
checkValue (ULam _ _ :@ _) v = throwError =<< ExpectedGotLambda <$> normalize v

checkValue (UPair t u :@ c) (VSigma x ((a, b) :@ d)) = do
  t' <- check' (t :@ c) (a :@ d)
  i <- declareE x Nothing
  defineE i (forget t' :@ c)
  u' <- check' (u :@ c) (b :@ (x, i):d)
  kPair (CSigma x a b :@ d) t' u'
checkValue (UPair _ _ :@ _) v = throwError =<< ExpectedGotPair <$> normalize v

checkValue (UEnumLabel l :@ _) (VEnum lbls)
  | l `elem` lbls = kEnumLabel (emptyC $ CEnum lbls) l
checkValue (UEnumLabel l :@ _) v =
  throwError =<< ExpectedGotLabel <$> pure l <*> normalize v

-- these rules are copied from the original and I do not 100%
--   understand their absence of other cases

checkValue (UBox t :@ c) (VLift (ty :@ d)) = do
  t' <- check' (t :@ c) (ty :@ d)
  kBox (CLift ty :@ d) t'

checkValue (UFold t :@ c) (VRec (ty :@ d)) = do
  forceTyV <- eval' (CForce ty :@ d)
  t' <- checkValue (t :@ c) forceTyV
  kFold (CRec ty :@ d) t'

-- ... the rest can
checkValue t v = do 
  t' <- infer t
  let ty :@ c = typeOf t'
  v' <- eval' (forget ty :@ c)
  eq <- v .=. v'
  if eq
    then pure t'
    else throwError =<< Mismatch <$> normalize v <*> normalize v'

infer :: (MonadState Env m, MonadError TypeError m)
      => Closure (UTerm) -- the term
      -> m KTerm -- a term with a known type (Closure CType)

infer (ULet ctxt t :@ c) = do
  (ctxt' :@ c') <- checkContext (ctxt :@ c)
  t' <- infer (t :@ c')
  kLet (typeOf t') ctxt' t'

infer (UType :@ _) = kType (emptyC CType)

infer (UVar x :@ c) = gets (lookupSE x c) >>= \case
  Just (EnvEntry _ (Just ty) _, _) -> kVar ty x
  _ -> throwError $ Undeclared x

infer (UPi x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC CType)
  i <- declareE x $ Just (forget ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC CType)
  kPi (emptyC CType) x ty' t'

infer (USigma x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC CType)
  i <- declareE x $ Just (forget ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC CType)
  kSigma (emptyC CType) x ty' t'

infer (UEnum lbls :@ _) = go Set.empty lbls where
  go _ [] = kEnum (emptyC CType) lbls
  go seen (l:ls) = if Set.member l seen
    then throwError $ DuplicateLabel l
    else go (Set.insert l seen) ls

infer (ULift t :@ c) = do
  t' <- check' (t :@ c) (emptyC CType)
  kLift (emptyC CType) t'

infer (UBox t :@ c) = do
  t' <- infer (t :@ c)
  let ty :@ c' = typeOf t'
  kBox (CLift ty :@ c') t'

infer (URec t :@ c) = do
  t' <- check' (t :@ c) (emptyC $ CLift CType)
  kRec (emptyC CType) t'

infer (UFold t :@ c) = do
  t' <- infer (t :@ c)
  let ty :@ c' = typeOf t'
  kFold (CRec (CBox ty) :@ c') t'

infer (UApp f t :@ c) = do
  f' <- infer (f :@ c)
  fTyV <- eval' (typeOf f')
  case fTyV of
    VPi x ((piArgTy, piResTy) :@ d) -> do
      t' <- check' (t :@ c) (piArgTy :@ d)
      i <- declareE x Nothing
      defineE i (forget t' :@ c)
      kApp (piResTy :@ (x, i):d) f' t'
    _ -> throwError =<< ExpectedPiType <$> normalize fTyV

infer (UForce t :@ c) = do
  t' <- infer (t :@ c)
  tyV <- eval' (typeOf t')
  case tyV of
    VLift tyBase -> kForce tyBase t'
    _ -> throwError =<< ExpectedLiftedType <$> normalize tyV

-- handle non-inferable cases
infer t = throwError $ NotInferable t

runCheck :: Env
         -> UTerm
         -> Closure (CTerm)
         -> Either TypeError KTerm
runCheck e t ty = evalState (runExceptT $ check t ty) e

runCheck' :: Env
          -> Closure (UTerm)
          -> Closure (CTerm)
          -> Either TypeError KTerm
runCheck' e t ty = evalState (runExceptT $ check' t ty) e

runInfer :: Env
         -> Closure (UTerm)
         -> Either TypeError KTerm
runInfer e t = evalState (runExceptT $ infer t) e

checkStmt :: (MonadState Env m, MonadError TypeError m)
          => Closure (Stmt 'Unchecked)
          -> Set.Set Ident
          -> Set.Set Ident
          -> m (Closure (Stmt 'KnownType), Set.Set Ident, Set.Set Ident)
checkStmt (Declare x ty :@ c) decls defns = if Set.member x decls
  then throwError $ DuplicateDeclare x
  else do
    ty' <- check' (ty :@ c) (emptyC CType)
    i <- declareE x (Just (forget ty' :@ c))
    pure (Declare x ty' :@ (x, i):c, Set.insert x decls, defns)
checkStmt (Define x t :@ c) decls defns = if Set.member x defns
  then throwError $ DuplicateDefine x
  else if not (Set.member x decls)
    then throwError $ Undeclared x
    else do
      Just (EnvEntry _ (Just ty) _, i) <- gets (lookupSE x c)
      t' <- check' (t :@ c) ty
      defineE i (forget t' :@ c)
      pure (Define x t' :@ c, decls, Set.insert x defns)
checkStmt (DeclareDefine x ty t :@ c) decls defns = do
  (Declare _ ty' :@ c', decls', defns') <-
    checkStmt (Declare x ty :@ c) decls defns
  (Define _ t' :@ c'', decls'', defns'') <-
    checkStmt (Define x t :@ c') decls' defns'
  pure (DeclareDefine x ty' t' :@ c'', decls'', defns'')

checkContext :: (MonadState Env m, MonadError TypeError m)
             => Closure (Context 'Unchecked)
             -> m (Closure (Context 'KnownType))
checkContext = go Set.empty Set.empty where
  go :: (MonadState Env m, MonadError TypeError m)
     => Set.Set Ident
     -> Set.Set Ident
     -> Closure (Context 'Unchecked)
     -> m (Closure (Context 'KnownType))

  go decls defns ([] :@ c) =
    case Set.lookupMin (Set.difference decls defns) of
      Nothing -> pure ([] :@ c)
      Just x -> throwError $ Undefined x

  go decls defns (stmt:rest :@ c) = do
    (stmt' :@ c', decls', defns') <- checkStmt (stmt :@ c) decls defns
    (rest' :@ c'') <- go decls' defns' (rest :@ c')
    pure (stmt':rest' :@ c'')

checkProgram :: (MonadState Env m, MonadError TypeError m)
             => Context 'Unchecked
             -> m (Context 'KnownType)
checkProgram = (fmap (\(x :@ _) -> x)) . checkContext . emptyC

typeOf :: KTerm -> Closure CTerm
typeOf (KLet ty _ _ _) = ty
typeOf (KType ty _) = ty
typeOf (KVar ty _ _) = ty
typeOf (KPi ty _ _ _ _) = ty
typeOf (KSigma ty _ _ _ _) = ty
typeOf (KLam ty _ _ _) = ty
typeOf (KPair ty _ _ _) = ty
typeOf (KEnum ty _ _) = ty
typeOf (KEnumLabel ty _ _) = ty
typeOf (KLift ty _ _) = ty
typeOf (KBox ty _ _) = ty
typeOf (KRec ty _ _) = ty
typeOf (KFold ty _ _) = ty
typeOf (KApp ty _ _ _) = ty
typeOf (KSplit ty _ _ _ _ _) = ty
typeOf (KCase ty _ _ _) = ty
typeOf (KForce ty _ _) = ty
typeOf (KUnfold ty _ _ _ _) = ty
typeOf (TermX v) = absurd v

typeOfE :: KTerm -> (Closure CTerm, Env)
typeOfE (KLet ty env _ _) = (ty, env)
typeOfE (KType ty env) = (ty, env)
typeOfE (KVar ty env _) = (ty, env)
typeOfE (KPi ty env _ _ _) = (ty, env)
typeOfE (KSigma ty env _ _ _) = (ty, env)
typeOfE (KLam ty env _ _) = (ty, env)
typeOfE (KPair ty env _ _) = (ty, env)
typeOfE (KEnum ty env _) = (ty, env)
typeOfE (KEnumLabel ty env _) = (ty, env)
typeOfE (KLift ty env _) = (ty, env)
typeOfE (KBox ty env _) = (ty, env)
typeOfE (KRec ty env _) = (ty, env)
typeOfE (KFold ty env _) = (ty, env)
typeOfE (KApp ty env _ _) = (ty, env)
typeOfE (KSplit ty env _ _ _ _) = (ty, env)
typeOfE (KCase ty env _ _) = (ty, env)
typeOfE (KForce ty env _) = (ty, env)
typeOfE (KUnfold ty env _ _ _) = (ty, env)
typeOfE (TermX v) = absurd v

type instance XLet 'KnownType = (Closure CTerm, Env)
type instance XType 'KnownType = (Closure CTerm, Env)
type instance XVar 'KnownType = (Closure CTerm, Env)
type instance XPi 'KnownType = (Closure CTerm, Env)
type instance XSigma 'KnownType = (Closure CTerm, Env)
type instance XLam 'KnownType = (Closure CTerm, Env)
type instance XPair 'KnownType = (Closure CTerm, Env)
type instance XEnum 'KnownType = (Closure CTerm, Env)
type instance XEnumLabel 'KnownType = (Closure CTerm, Env)
type instance XLift 'KnownType = (Closure CTerm, Env)
type instance XBox 'KnownType = (Closure CTerm, Env)
type instance XRec 'KnownType = (Closure CTerm, Env)
type instance XFold 'KnownType = (Closure CTerm, Env)
type instance XApp 'KnownType = (Closure CTerm, Env)
type instance XSplit 'KnownType = (Closure CTerm, Env)
type instance XCase 'KnownType = (Closure CTerm, Env)
type instance XForce 'KnownType = (Closure CTerm, Env)
type instance XUnfold 'KnownType = (Closure CTerm, Env)
type instance XTerm 'KnownType = Void

pattern KLet :: Closure CTerm -> Env -> Context 'KnownType -> KTerm -> KTerm
pattern KLet kTy env ctxt t = Let (kTy, env) ctxt t

kLet :: MonadState Env m => Closure CTerm -> Context 'KnownType -> KTerm -> m KTerm
kLet kTy ctxt t =
  KLet <$> pure kTy <*> get <*> pure ctxt <*> pure t

pattern KType :: Closure CTerm -> Env -> KTerm
pattern KType kTy env = Type (kTy, env)

kType :: MonadState Env m => Closure CTerm -> m KTerm
kType kTy = KType <$> pure kTy <*> get

pattern KVar :: Closure CTerm -> Env -> Ident -> KTerm
pattern KVar kTy env x = Var (kTy, env) x

kVar :: MonadState Env m => Closure CTerm -> Ident -> m KTerm
kVar kTy x = KVar <$> pure kTy <*> get <*> pure x

pattern KPi :: Closure CTerm -> Env -> Ident -> KTerm -> KTerm -> KTerm
pattern KPi kTy env x ty t = Pi (kTy, env) x ty t

kPi :: MonadState Env m => Closure CTerm -> Ident -> KTerm -> KTerm -> m KTerm
kPi kTy x ty t =
  KPi <$> pure kTy <*> get <*> pure x <*> pure ty <*> pure t

pattern KSigma :: Closure CTerm -> Env -> Ident -> KTerm -> KTerm -> KTerm
pattern KSigma kTy env x ty t = Sigma (kTy, env) x ty t

kSigma :: MonadState Env m => Closure CTerm -> Ident -> KTerm -> KTerm -> m KTerm
kSigma kTy x ty t =
  KSigma <$> pure kTy <*> get <*> pure x <*> pure ty <*> pure t

pattern KLam :: Closure CTerm -> Env -> Ident -> KTerm -> KTerm
pattern KLam kTy env x t = Lam (kTy, env) x t

kLam :: MonadState Env m => Closure CTerm -> Ident -> KTerm -> m KTerm
kLam kTy x t = KLam <$> pure kTy <*> get <*> pure x <*> pure t

pattern KPair :: Closure CTerm -> Env -> KTerm -> KTerm -> KTerm
pattern KPair kTy env t u = Pair (kTy, env) t u

kPair :: MonadState Env m => Closure CTerm -> KTerm -> KTerm -> m KTerm
kPair kTy t u = KPair <$> pure kTy <*> get <*> pure t <*> pure u

pattern KEnum :: Closure CTerm -> Env -> [Label] -> KTerm
pattern KEnum kTy env lbls = Enum (kTy, env) lbls

kEnum :: MonadState Env m => Closure CTerm -> [Label] -> m KTerm
kEnum kTy lbls = KEnum <$> pure kTy <*> get <*> pure lbls

pattern KEnumLabel :: Closure CTerm -> Env -> Label -> KTerm
pattern KEnumLabel kTy env l = EnumLabel (kTy, env) l

kEnumLabel :: MonadState Env m => Closure CTerm -> Label -> m KTerm
kEnumLabel kTy l = KEnumLabel <$> pure kTy <*> get <*> pure l

pattern KLift :: Closure CTerm -> Env -> KTerm -> KTerm
pattern KLift kTy env ty = Lift (kTy, env) ty

kLift :: MonadState Env m => Closure CTerm -> KTerm -> m KTerm
kLift kTy ty = KLift <$> pure kTy <*> get <*> pure ty

pattern KBox :: Closure CTerm -> Env -> KTerm -> KTerm
pattern KBox kTy env t = Box (kTy, env) t

kBox :: MonadState Env m => Closure CTerm -> KTerm -> m KTerm
kBox kTy t = KBox <$> pure kTy <*> get <*> pure t

pattern KRec :: Closure CTerm -> Env -> KTerm -> KTerm
pattern KRec kTy env ty = Rec (kTy, env) ty

kRec :: MonadState Env m => Closure CTerm -> KTerm -> m KTerm
kRec kTy ty = KRec <$> pure kTy <*> get <*> pure ty

pattern KFold :: Closure CTerm -> Env -> KTerm -> KTerm
pattern KFold kTy env t = Fold (kTy, env) t

kFold :: MonadState Env m => Closure CTerm -> KTerm -> m KTerm
kFold kTy t = KFold <$> pure kTy <*> get <*> pure t

pattern KApp :: Closure CTerm -> Env -> KTerm -> KTerm -> KTerm
pattern KApp kTy env f x = App (kTy, env) f x

kApp :: MonadState Env m => Closure CTerm -> KTerm -> KTerm -> m KTerm
kApp kTy f x = KApp <$> pure kTy <*> get <*> pure f <*> pure x

pattern KSplit :: Closure CTerm -> Env -> KTerm -> Ident -> Ident -> KTerm -> KTerm
pattern KSplit kTy env t x y u = Split (kTy, env) t x y u

kSplit :: MonadState Env m => Closure CTerm -> KTerm -> Ident -> Ident -> KTerm -> m KTerm
kSplit kTy t x y u =
  KSplit <$> pure kTy
         <*> get
         <*> pure t
         <*> pure x
         <*> pure y
         <*> pure u

pattern KCase :: Closure CTerm -> Env -> KTerm -> [(Label, KTerm)] -> KTerm
pattern KCase kTy env t cases = Case (kTy, env) t cases

kCase :: MonadState Env m => Closure CTerm -> KTerm -> [(Label, KTerm)] -> m KTerm
kCase kTy t cases =
  KCase <$> pure kTy
        <*> get
        <*> pure t
        <*> pure cases

pattern KForce :: Closure CTerm -> Env -> KTerm -> KTerm
pattern KForce kTy env t = Force (kTy, env) t

kForce :: MonadState Env m => Closure CTerm -> KTerm -> m KTerm
kForce kTy t = KForce <$> pure kTy <*> get <*> pure t

pattern KUnfold :: Closure CTerm -> Env -> KTerm -> Ident -> KTerm -> KTerm
pattern KUnfold kTy env t x u = Unfold (kTy, env) t x u

kUnfold :: MonadState Env m => Closure CTerm -> KTerm -> Ident -> KTerm -> m KTerm
kUnfold kTy t x u =
  KUnfold <$> pure kTy
          <*> get
          <*> pure t
          <*> pure x
          <*> pure u

{-# COMPLETE KLet, KType, KVar, KPi, KSigma,
   KLam, KPair, KEnum, KEnumLabel, KLift, KBox, KRec,
   KFold, KApp, KSplit, KCase, KForce, KUnfold #-}

deriving instance Show (TermX 'KnownType)

deriving instance Show (Stmt 'KnownType) 
