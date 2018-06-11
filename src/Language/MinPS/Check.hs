{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Check (
    TypeError
  , check
  , check'
  , infer
  , runCheck
  , runCheck'
  , runInfer
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
  | ExpectedGotLambda Value
  | ExpectedGotPair Value
  | ExpectedGotLabel Label Value
  | ExpectedPiType Value
  | ExpectedSigmaType Value
  | ExpectedLiftedType Value
  | ExpectedRecType Value
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
          -- this seems insane.
          i <- declareE x (Just (a :@ d))
          defineE i (Var x :@ (x, i):c)
          j <- declareE y (Just (b :@ (z, i):d))
          let c' = (y, j):(x, i):c
          case tV of
            -- I have even less clue here
            VNeutral (NVar k) -> locally $ do
              defineE k (Pair (Var x) (Var y) :@ c')
              check' (u :@ c') ty
            _ -> check' (u :@ c') ty
        _ -> throwError $ ExpectedSigmaType tyV

check' (Case t cases :@ c) ty = error "TODO: constraints"

check' (Force t :@ c) (ty :@ d) = check' (t :@ c) (Lift ty :@ d)

check' (Unfold t x u :@ c) ty = do
  (ty', t') <- infer (t :@ c)
  tyV <- eval' ty'
  case tyV of
    VRec (a :@ d) -> do
      tV <- eval' (t' :@ c)
      i <- declareE x (Just (Force a :@ d))
      let c' = (x, i):c
      case tV of
        VNeutral (NVar k) -> locally $ do
          defineE k (Fold (Var x) :@ c')
          check' (u :@ c') ty
        _ -> check' (u :@ c') ty
    _ -> throwError $ ExpectedRecType tyV

-- the default case
check' t ty = eval' ty >>= checkValue t

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

checkValue (Box t :@ c) (VLift ty) = check' (t :@ c) ty

checkValue (Fold t :@ c) (VRec (ty :@ d)) = do
  forceTyV <- eval' (Force ty :@ d)
  checkValue (t :@ c) forceTyV

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
