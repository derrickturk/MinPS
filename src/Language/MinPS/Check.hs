{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Check (
    TypeError(..)
  , check
  , check'
  , checkStmt
  , infer
  , runCheck
  , runCheck'
  , runInfer
) where

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Normalize

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
  pure $ KLet ty ctxt' t'

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
          pure $ KSplit ty t' x y u'
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
          pure $ KCase ty t' (zip lbls' cases')
          where
            checkCase (l, u) = withConstraint
              (forget t' :@ c) l (check' (u :@ c) ty)
    _ -> throwError =<< ExpectedEnumType <$> normalize tyV

check' (UForce t :@ c) (ty :@ d) = do
  t' <- check' (t :@ c) (CLift ty :@ d)
  pure $ KForce (ty :@ d) t'

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
      pure $ KUnfold ty t' x u'
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
  pure $ KLam (CPi y ty u :@ d) x t'
checkValue (ULam _ _ :@ _) v = throwError =<< ExpectedGotLambda <$> normalize v

checkValue (UPair t u :@ c) (VSigma x ((a, b) :@ d)) = do
  t' <- check' (t :@ c) (a :@ d)
  i <- declareE x Nothing
  defineE i (forget t' :@ c)
  u' <- check' (u :@ c) (b :@ (x, i):d)
  pure $ KPair (CSigma x a b :@ d) t' u'
checkValue (UPair _ _ :@ _) v = throwError =<< ExpectedGotPair <$> normalize v

checkValue (UEnumLabel l :@ _) (VEnum lbls)
  | l `elem` lbls = pure $ KEnumLabel (emptyC $ CEnum lbls) l
checkValue (UEnumLabel l :@ _) v =
  throwError =<< ExpectedGotLabel <$> pure l <*> normalize v

-- these rules are copied from the original and I do not 100%
--   understand their absence of other cases

checkValue (UBox t :@ c) (VLift (ty :@ d)) = do
  t' <- check' (t :@ c) (ty :@ d)
  pure $ KBox (CLift ty :@ d) t'

checkValue (UFold t :@ c) (VRec (ty :@ d)) = do
  forceTyV <- eval' (CForce ty :@ d)
  t' <- checkValue (t :@ c) forceTyV
  pure $ KFold (CRec ty :@ d) t'

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
  pure $ KLet (typeOf t') ctxt' t'

infer (UType :@ _) = pure $ KType (emptyC CType)

infer (UVar x :@ c) = gets (lookupSE x c) >>= \case
  Just (EnvEntry _ (Just ty) _, _) -> pure $ KVar ty x
  _ -> throwError $ Undeclared x

infer (UPi x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC CType)
  i <- declareE x $ Just (forget ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC CType)
  pure $ KPi (emptyC CType) x ty' t'

infer (USigma x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC CType)
  i <- declareE x $ Just (forget ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC CType)
  pure $ KSigma (emptyC CType) x ty' t'

infer (UEnum lbls :@ _) = go Set.empty lbls where
  go _ [] = pure $ KEnum (emptyC CType) lbls
  go seen (l:ls) = if Set.member l seen
    then throwError $ DuplicateLabel l
    else go (Set.insert l seen) ls

infer (ULift t :@ c) = do
  t' <- check' (t :@ c) (emptyC CType)
  pure $ KLift (emptyC CType) t'

infer (UBox t :@ c) = do
  t' <- infer (t :@ c)
  let ty :@ c' = typeOf t'
  pure $ KBox (CLift ty :@ c') t'

infer (URec t :@ c) = do
  t' <- check' (t :@ c) (emptyC $ CLift CType)
  pure $ KRec (emptyC CType) t'

infer (UFold t :@ c) = do
  t' <- infer (t :@ c)
  let ty :@ c' = typeOf t'
  pure $ KFold (CRec (CBox ty) :@ c') t'

infer (UApp f t :@ c) = do
  f' <- infer (f :@ c)
  fTyV <- eval' (typeOf f')
  case fTyV of
    VPi x ((piArgTy, piResTy) :@ d) -> do
      t' <- check' (t :@ c) (piArgTy :@ d)
      i <- declareE x Nothing
      defineE i (forget t' :@ c)
      pure $ KApp (piResTy :@ (x, i):d) f' t'
    _ -> throwError =<< ExpectedPiType <$> normalize fTyV

infer (UForce t :@ c) = do
  t' <- infer (t :@ c)
  tyV <- eval' (typeOf t')
  case tyV of
    VLift tyBase -> pure $ KForce tyBase t'
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
