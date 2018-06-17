{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Check (
    TypeError
  , check
  , check'
  , checkStmt
  , infer
  , runCheck
  , runCheck'
  , runInfer
  , typeErrorPretty
) where

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Normalize

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as Set
import qualified Data.Text as T

data TypeError =
    Mismatch Value Value
  | ExpectedGotLambda Value
  | ExpectedGotPair Value
  | ExpectedGotLabel Label Value
  | ExpectedPiType Value
  | ExpectedSigmaType Value
  | ExpectedEnumType Value
  | ExpectedLiftedType Value
  | ExpectedRecType Value
  | Undeclared Ident
  | Undefined Ident
  | DuplicateDeclare Ident
  | DuplicateDefine Ident
  | DuplicateLabel Label
  | LabelsMismatch [Label] [Label]
  | NotInferable (Closure (Term 'Unchecked))
  deriving Show

check :: (MonadState Env m, MonadError TypeError m)
      => Term 'Unchecked
      -> Closure (Term 'Checked)
      -> m (Term 'Checked)
check t = check' $ emptyC t

check' :: (MonadState Env m, MonadError TypeError m)
       => Closure (Term 'Unchecked)
       -> Closure (Term 'Checked)
       -> m (Term 'Checked)

-- as in the original, we "first handle the cases that may potentially
-- change the environment". I am not 100% sure this split is necessary.
check' (Let ctxt t :@ c) ty = do
  (ctxt' :@ c') <- checkContext (ctxt :@ c)
  t' <- check' (t :@ c') ty
  pure $ Let ctxt' t'

check' (Split t x y u :@ c) ty
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
              defineE k (Pair (Var x) (Var y) :@ c')
              check' (u :@ c') ty
            _ -> check' (u :@ c') ty
          pure $ Split t' x y u'
        _ -> throwError $ ExpectedSigmaType tyV

check' (Case t cases :@ c) ty = do
  (ty', t') <- infer (t :@ c)
  tyV <- eval' ty'
  case tyV of
    VEnum lbls -> let lbls' = fmap fst cases in
      if Set.fromList lbls /= Set.fromList lbls'
        then throwError $ LabelsMismatch lbls' lbls
        else do
          cases' <- mapM checkCase cases
          pure $ Case t' (zip lbls' cases')
          where
            checkCase (l, u) = withConstraint (t' :@ c) l (check' (u :@ c) ty)
    _ -> throwError $ ExpectedEnumType tyV

check' (Force t :@ c) (ty :@ d) = do
  t' <- check' (t :@ c) (Lift ty :@ d)
  pure $ Force t'

check' (Unfold t x u :@ c) ty = do
  (ty', t') <- infer (t :@ c)
  tyV <- eval' ty'
  case tyV of
    VRec (a :@ d) -> do
      tV <- eval' (t' :@ c)
      i <- declareE x (Just (Force a :@ d))
      let c' = (x, i):c
      u' <- case tV of
        VNeutral (NVar k) -> locally $ do
          defineE k (Fold (Var x) :@ c')
          check' (u :@ c') ty
        _ -> check' (u :@ c') ty
      pure $ Unfold t' x u'
    _ -> throwError $ ExpectedRecType tyV

-- the default case
check' t ty = do
  eval' ty >>= checkValue t

checkValue :: (MonadState Env m, MonadError TypeError m)
           => Closure (Term 'Unchecked)
           -> Value
           -> m (Term 'Checked)

-- some cases can't be inferred...
checkValue (Lam x t :@ c) (VPi y ((ty, u) :@ d)) = do
  i <- declareE x (Just (ty :@ d))
  t' <- check' (t :@ (x, i):c) (u :@ (y, i):d)
  pure $ Lam x t'
checkValue (Lam _ _ :@ _) v = throwError $ ExpectedGotLambda v

checkValue (Pair t u :@ c) (VSigma x ((a, b) :@ d)) = do
  t' <- check' (t :@ c) (a :@ d)
  i <- declareE x Nothing
  defineE i (t' :@ c)
  u' <- check' (u :@ c) (b :@ (x, i):d)
  pure $ Pair t' u'
checkValue (Pair _ _ :@ _) v = throwError $ ExpectedGotPair v

checkValue (EnumLabel l :@ _) (VEnum lbls)
  | l `elem` lbls = pure $ EnumLabel l
checkValue (EnumLabel l :@ _) v = throwError $ ExpectedGotLabel l v

-- these rules are copied from the original and I do not 100%
--   understand their absence of other cases

checkValue (Box t :@ c) (VLift ty) = do
  t' <- check' (t :@ c) ty
  pure $ Box t'

checkValue (Fold t :@ c) (VRec (ty :@ d)) = do
  forceTyV <- eval' (Force ty :@ d)
  t' <- checkValue (t :@ c) forceTyV
  pure $ Fold t'

-- ... the rest can
checkValue t v = do 
  (ty, t') <- infer t
  v' <- eval' ty
  eq <- v .=. v'
  if eq then pure t' else throwError (Mismatch v v')

infer :: (MonadState Env m, MonadError TypeError m)
      => Closure (Term 'Unchecked) -- the term
      -> m (Closure (Term 'Checked), Term 'Checked) -- the type + closure & the term

infer (Let ctxt t :@ c) = do
  (ctxt' :@ c') <- checkContext (ctxt :@ c)
  (ty, t') <- infer (t :@ c')
  pure (ty, Let ctxt' t')

infer (Type :@ _) = pure (emptyC Type, Type)

infer (Var x :@ c) = gets (lookupSE x c) >>= \case
  Just (EnvEntry _ (Just ty) _, _) -> pure (ty, Var x)
  _ -> throwError $ Undeclared x

infer (Pi x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC Type)
  i <- declareE x $ Just (ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC Type)
  pure (emptyC Type, Pi x ty' t')

infer (Sigma x ty t :@ c) = do
  ty' <- check' (ty :@ c) (emptyC Type)
  i <- declareE x $ Just (ty' :@ c)
  t' <- check' (t :@ (x, i):c) (emptyC Type)
  pure (emptyC Type, Sigma x ty' t')

infer (Enum lbls :@ _) = go Set.empty lbls where
  go _ [] = pure (emptyC Type, Enum lbls)
  go seen (l:ls) = if Set.member l seen
    then throwError $ DuplicateLabel l
    else go (Set.insert l seen) ls

infer (Lift t :@ c) = do
  t' <- check' (t :@ c) (emptyC Type)
  pure (emptyC Type, Lift t')

infer (Box t :@ c) = do
  (ty :@ c', t') <- infer (t :@ c)
  pure (Lift ty :@ c', Box t')

infer (Rec t :@ c) = do
  t' <- check' (t :@ c) (emptyC $ Lift Type)
  pure (emptyC Type, Rec t')

infer (Fold t :@ c) = do
  (ty :@ c', t') <- infer (t :@ c)
  pure (Rec (Box ty) :@ c', Fold t')

infer (App f t :@ c) = do
  (fTy, f') <- infer (f :@ c)
  fTyV <- eval' fTy
  case fTyV of
    VPi x ((piArgTy, pyResTy) :@ d) -> do
      t' <- check' (t :@ c) (piArgTy :@ d)
      i <- declareE x Nothing
      defineE i (t' :@ c)
      pure (pyResTy :@ (x, i):d, App f' t')
    _ -> throwError $ ExpectedPiType fTyV

infer (Force t :@ c) = do
  (ty, t') <- infer (t :@ c)
  tyV <- eval' ty
  case tyV of
    VLift tyBase -> pure (tyBase, Force t')
    _ -> throwError $ ExpectedLiftedType tyV

-- handle non-inferable cases
infer t = throwError $ NotInferable t

runCheck :: Env
         -> Term 'Unchecked
         -> Closure (Term 'Checked)
         -> Either TypeError (Term 'Checked)
runCheck e t ty = evalState (runExceptT $ check t ty) e

runCheck' :: Env
          -> Closure (Term 'Unchecked)
          -> Closure (Term 'Checked)
          -> Either TypeError (Term 'Checked)
runCheck' e t ty = evalState (runExceptT $ check' t ty) e

runInfer :: Env
         -> Closure (Term 'Unchecked)
         -> Either TypeError (Closure (Term 'Checked), Term 'Checked)
runInfer e t = evalState (runExceptT $ infer t) e

checkStmt :: (MonadState Env m, MonadError TypeError m)
          => Closure (Stmt 'Unchecked)
          -> Set.Set Ident
          -> Set.Set Ident
          -> m (Closure (Stmt 'Checked), Set.Set Ident, Set.Set Ident)
checkStmt (Declare x ty :@ c) decls defns = if Set.member x decls
  then throwError $ DuplicateDeclare x
  else do
    ty' <- check' (ty :@ c) (emptyC Type)
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

typeErrorPretty :: (MonadState Env m) => TypeError -> m String
typeErrorPretty (Mismatch ex got) = do
  vExp <- normalize ex
  vGot <- normalize got
  pure $ "type mismatch:\n\texpected " ++ show vExp
    ++ "\n\tgot " ++ show vGot
typeErrorPretty (ExpectedGotLambda ex) = normalize ex >>=
  \vE -> pure $ "expected lambda; got " ++ show vE
typeErrorPretty (ExpectedGotPair ex) = normalize ex >>=
  \vE -> pure $ "expected pair; got " ++ show vE
typeErrorPretty (ExpectedGotLabel (MkLabel lbl) ex) = normalize ex >>=
  \vE -> pure $ "got label '" ++ T.unpack lbl ++ "; got " ++ show vE
typeErrorPretty (ExpectedPiType ex) = normalize ex >>=
  \vE -> pure $ "expected pi type; got " ++ show vE
typeErrorPretty (ExpectedSigmaType ex) = normalize ex >>=
  \vE -> pure $ "expected sigma type; got " ++ show vE
typeErrorPretty (ExpectedEnumType ex) = normalize ex >>=
  \vE -> pure $ "expected enum type; got " ++ show vE
typeErrorPretty (ExpectedLiftedType ex) = normalize ex >>=
  \vE -> pure $ "expected lifted type; got " ++ show vE
typeErrorPretty (ExpectedRecType ex) = normalize ex >>=
  \vE -> pure $ "expected Rec type; got " ++ show vE
typeErrorPretty (Undeclared (MkIdent x)) =
  pure $ "undeclared variable " ++ T.unpack x
typeErrorPretty (Undefined (MkIdent x)) =
  pure $ "undefined variable " ++ T.unpack x
typeErrorPretty (DuplicateDeclare (MkIdent x)) =
  pure $ "duplicate declarations for " ++ T.unpack x
typeErrorPretty (DuplicateDefine (MkIdent x)) =
  pure $ "duplicate definitions for " ++ T.unpack x
typeErrorPretty (DuplicateLabel (MkLabel l)) =
  pure $ "duplicate label " ++ T.unpack l
typeErrorPretty (LabelsMismatch ex got) =
  pure $ "labels mismatch; expected " ++ show ex
  ++ ", got " ++ show got
typeErrorPretty (NotInferable t) = pure $ "not inferable: " ++ show t
