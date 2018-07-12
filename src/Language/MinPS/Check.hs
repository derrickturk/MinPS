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
      -> m (CTerm)
check t = check' $ emptyC t

check' :: (MonadState Env m, MonadError TypeError m)
       => Closure (UTerm)
       -> Closure (CTerm)
       -> m (CTerm)

-- as in the original, we "first handle the cases that may potentially
-- change the environment". I am not 100% sure this split is necessary.
check' (ULet ctxt t :@ c) ty = do
  (ctxt' :@ c') <- checkContext (ctxt :@ c)
  t' <- check' (t :@ c') ty
  pure $ CLet ctxt' t'

check' (USplit t x y u :@ c) ty
  | x == y = throwError $ DuplicateDeclare y
  | otherwise = do
      (ty', t') <- infer (t :@ c)
      tyV <- eval' ty'
      case tyV of
        VSigma z ((a, b) :@ d) -> do
          tV <- eval' (t' :@ c)
          i <- declareE x (Just (a :@ d))
          j <- declareE y (Just (b :@ (z, i):d))
          let c' = (y, j):(x, i):c
          u' <- case tV of
            VNeutral (NVar k) -> locally $ do
              defineE k (CPair (CVar x) (CVar y) :@ c')
              check' (u :@ c') ty
            _ -> check' (u :@ c') ty
          pure $ CSplit t' x y u'
        _ -> throwError =<< ExpectedSigmaType <$> normalize tyV

check' (UCase t cases :@ c) ty = do
  (ty', t') <- infer (t :@ c)
  tyV <- eval' ty'
  case tyV of
    VEnum lbls -> let lbls' = fmap fst cases in
      if Set.fromList lbls /= Set.fromList lbls'
        then throwError $ LabelsMismatch lbls' lbls
        else do
          cases' <- mapM checkCase cases
          pure $ CCase t' (zip lbls' cases')
          where
            checkCase (l, u) = withConstraint (t' :@ c) l (check' (u :@ c) ty)
    _ -> throwError =<< ExpectedEnumType <$> normalize tyV

check' (UForce t :@ c) (ty :@ d) = do
  t' <- check' (t :@ c) (CLift ty :@ d)
  pure $ CForce t'

check' (UUnfold t x u :@ c) ty = do
  (ty', t') <- infer (t :@ c)
  tyV <- eval' ty'
  case tyV of
    VRec (a :@ d) -> do
      tV <- eval' (t' :@ c)
      i <- declareE x (Just (CForce a :@ d))
      let c' = (x, i):c
      u' <- case tV of
        VNeutral (NVar k) -> locally $ do
          defineE k (CFold (CVar x) :@ c')
          check' (u :@ c') ty
        _ -> check' (u :@ c') ty
      pure $ CUnfold t' x u'
    _ -> throwError =<< ExpectedRecType <$> normalize tyV

-- the default case
check' t ty = do
  eval' ty >>= checkValue t

checkValue :: (MonadState Env m, MonadError TypeError m)
           => Closure (UTerm)
           -> Value
           -> m (CTerm)

-- some cases can't be inferred...
checkValue (ULam x t :@ c) (VPi y ((ty, u) :@ d)) = do
  i <- declareE x (Just (ty :@ d))
  t' <- check' (t :@ (x, i):c) (u :@ (y, i):d)
  pure $ CLam x t'
checkValue (ULam _ _ :@ _) v = throwError =<< ExpectedGotLambda <$> normalize v

checkValue (UPair t u :@ c) (VSigma x ((a, b) :@ d)) = do
  t' <- check' (t :@ c) (a :@ d)
  i <- declareE x Nothing
  defineE i (t' :@ c)
  u' <- check' (u :@ c) (b :@ (x, i):d)
  pure $ CPair t' u'
checkValue (UPair _ _ :@ _) v = throwError =<< ExpectedGotPair <$> normalize v

checkValue (UEnumLabel l :@ _) (VEnum lbls)
  | l `elem` lbls = pure $ CEnumLabel l
checkValue (CEnumLabel l :@ _) v =
  throwError =<< ExpectedGotLabel <$> pure l <*> normalize v

-- these rules are copied from the original and I do not 100%
--   understand their absence of other cases

checkValue (UBox t :@ c) (VLift ty) = do
  t' <- check' (t :@ c) ty
  pure $ CBox t'

checkValue (UFold t :@ c) (VRec (ty :@ d)) = do
  forceTyV <- eval' (CForce ty :@ d)
  t' <- checkValue (t :@ c) forceTyV
  pure $ CFold t'

-- ... the rest can
checkValue t v = do 
  (ty, t') <- infer t
  v' <- eval' ty
  eq <- v .=. v'
  if eq
    then pure t'
    else throwError =<< Mismatch <$> normalize v <*> normalize v'

infer :: (MonadState Env m, MonadError TypeError m)
      => Closure (UTerm) -- the term
      -> m (Closure (CTerm), CTerm) -- the type + closure & the term

infer (ULet ctxt t :@ c) = do
  (ctxt' :@ c') <- checkContext (ctxt :@ c)
  (ty, t') <- infer (t :@ c')
  pure (ty, CLet ctxt' t')

infer (UType :@ _) = pure (emptyC CType, CType)

infer (UVar x :@ c) = gets (lookupSE x c) >>= \case
  Just (EnvEntry _ (Just ty) _, _) -> pure (ty, CVar x)
  _ -> throwError $ Undeclared x

infer (UPi x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC CType)
  i <- declareE x $ Just (ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC CType)
  pure (emptyC CType, CPi x ty' t')

infer (USigma x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC CType)
  i <- declareE x $ Just (ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC CType)
  pure (emptyC CType, CSigma x ty' t')

infer (UEnum lbls :@ _) = go Set.empty lbls where
  go _ [] = pure (emptyC CType, CEnum lbls)
  go seen (l:ls) = if Set.member l seen
    then throwError $ DuplicateLabel l
    else go (Set.insert l seen) ls

infer (ULift t :@ c) = do
  t' <- check' (t :@ c) (emptyC CType)
  pure (emptyC CType, CLift t')

infer (UBox t :@ c) = do
  (ty :@ c', t') <- infer (t :@ c)
  pure (CLift ty :@ c', CBox t')

infer (URec t :@ c) = do
  t' <- check' (t :@ c) (emptyC $ CLift CType)
  pure (emptyC CType, CRec t')

infer (UFold t :@ c) = do
  (ty :@ c', t') <- infer (t :@ c)
  pure (CRec (CBox ty) :@ c', CFold t')

infer (UApp f t :@ c) = do
  (fTy, f') <- infer (f :@ c)
  fTyV <- eval' fTy
  case fTyV of
    VPi x ((piArgTy, pyResTy) :@ d) -> do
      t' <- check' (t :@ c) (piArgTy :@ d)
      i <- declareE x Nothing
      defineE i (t' :@ c)
      pure (pyResTy :@ (x, i):d, CApp f' t')
    _ -> throwError =<< ExpectedPiType <$> normalize fTyV

infer (UForce t :@ c) = do
  (ty, t') <- infer (t :@ c)
  tyV <- eval' ty
  case tyV of
    VLift tyBase -> pure (tyBase, CForce t')
    _ -> throwError =<< ExpectedLiftedType <$> normalize tyV

-- handle non-inferable cases
infer t = throwError $ NotInferable t

runCheck :: Env
         -> UTerm
         -> Closure (CTerm)
         -> Either TypeError (CTerm)
runCheck e t ty = evalState (runExceptT $ check t ty) e

runCheck' :: Env
          -> Closure (UTerm)
          -> Closure (CTerm)
          -> Either TypeError (CTerm)
runCheck' e t ty = evalState (runExceptT $ check' t ty) e

runInfer :: Env
         -> Closure (UTerm)
         -> Either TypeError (Closure (CTerm), CTerm)
runInfer e t = evalState (runExceptT $ infer t) e

checkStmt :: (MonadState Env m, MonadError TypeError m)
          => Closure (Stmt 'Unchecked)
          -> Set.Set Ident
          -> Set.Set Ident
          -> m (Closure (Stmt 'Checked), Set.Set Ident, Set.Set Ident)
checkStmt (Declare x ty :@ c) decls defns = if Set.member x decls
  then throwError $ DuplicateDeclare x
  else do
    ty' <- check' (ty :@ c) (emptyC CType)
    i <- declareE x (Just (ty' :@ c))
    pure (Declare x ty' :@ (x, i):c, Set.insert x decls, defns)
checkStmt (Define x t :@ c) decls defns = if Set.member x defns
  then throwError $ DuplicateDefine x
  else if not (Set.member x decls)
    then throwError $ Undeclared x
    else do
      Just (EnvEntry _ (Just ty) _, i) <- gets (lookupSE x c)
      t' <- check' (t :@ c) ty
      defineE i (t' :@ c)
      pure (Define x t' :@ c, decls, Set.insert x defns)
checkStmt (DeclareDefine x ty t :@ c) decls defns = do
  (Declare _ ty' :@ c', decls', defns') <-
    checkStmt (Declare x ty :@ c) decls defns
  (Define _ t' :@ c'', decls'', defns'') <-
    checkStmt (Define x t :@ c') decls' defns'
  pure (DeclareDefine x ty' t' :@ c'', decls'', defns'')

checkContext :: (MonadState Env m, MonadError TypeError m)
             => Closure (Context 'Unchecked)
             -> m (Closure (Context 'Checked))
checkContext = go Set.empty Set.empty where
  go :: (MonadState Env m, MonadError TypeError m)
     => Set.Set Ident
     -> Set.Set Ident
     -> Closure (Context 'Unchecked)
     -> m (Closure (Context 'Checked))

  go decls defns ([] :@ c) =
    case Set.lookupMin (Set.difference decls defns) of
      Nothing -> pure ([] :@ c)
      Just x -> throwError $ Undefined x

  go decls defns (stmt:rest :@ c) = do
    (stmt' :@ c', decls', defns') <- checkStmt (stmt :@ c) decls defns
    (rest' :@ c'') <- go decls' defns' (rest :@ c')
    pure (stmt':rest' :@ c'')
