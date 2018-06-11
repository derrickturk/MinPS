{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Check (
    TypeError
  , check
  , check'
  , infer
    {--
  , MonadCheck(..)
  , TypedRecEnv
  , emptyTypedRecEnv
  , Check
  , runCheck
  , evalCheck
  , execCheck
  --}
) where

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Environment
import Language.MinPS.Eval
import Language.MinPS.Equals

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as Set

data TypeError =
    Mismatch Value Value
  | ExpectedPiType Value
  | ExpectedLiftedType Value
  | Undeclared Ident
  | Undefined Ident
  | DuplicateDeclare Ident
  | DuplicateDefine Ident
  | DuplicateLabel Label
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

-- TODO: env-altering cases

check' t ty = eval' ty >>= checkValue t

checkValue :: (MonadState Env m, MonadError TypeError m)
           => Closure (Term 'Unchecked)
           -> Value
           -> m (Term 'Checked)

-- TODO: un-inferable cases

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

  go decls defns ((Declare x ty):rest :@ c) = if Set.member x decls
    then throwError $ DuplicateDeclare x
    else do
      ty' <- check' (ty :@ c) (emptyC Type)
      i <- declareE x (Just (ty' :@ c))
      (rest' :@ c') <- go (Set.insert x decls) defns (rest :@ (x, i):c)
      pure ((Declare x ty'):rest' :@ c')

  go decls defns ((Define x t):rest :@ c) = if Set.member x defns
    then throwError $ DuplicateDefine x
    else if not (Set.member x decls)
      then throwError $ Undeclared x
      else do
        Just (EnvEntry _ (Just ty) _, i) <- gets (lookupSE x c)
        t' <- check' (t :@ c) ty
        defineE i (t' :@ c)
        (rest' :@ c') <- go decls (Set.insert x defns) (rest :@ c)
        pure ((Define x t'):rest' :@ c')
