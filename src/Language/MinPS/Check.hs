{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Check (
    TypeError
  , MonadCheck(..)
  , check
  , infer
  , TypedRecEnv
  , emptyTypedRecEnv
  , Check
  , runCheck
  , evalCheck
  , execCheck
) where

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Eval

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Sequence as S
import qualified Data.Set as Set
import qualified Data.Text as T

-- we're going to use the Closure structure to store the types
--   (as WHNF forms) of bound values during checking in addition
--   to their values as in Eval
-- we'll adapt the RecEnv idea and track two environments, the environment
--   of values and the environment of types, for possibly
--   mutually-recursive bindings

data TypeError =
    Mismatch (Term 'Unchecked) Value
  | Undeclared T.Text
  | Undefined T.Text
  | DuplicateDeclare T.Text
  | DuplicateDefine T.Text
  deriving Show

-- wait, do I want this?
class (MonadEval m, MonadError TypeError m) => MonadCheck m where
  getBoundType :: RecBinding -> m (Maybe (T.Text, Closure, Term 'Checked))
  addBoundType :: (T.Text, Closure, Term 'Checked) -> m RecBinding

check :: Term 'Unchecked -> Value -> Check (Term 'Checked)
check = check' []

check' :: Closure
       -> Term 'Unchecked
       -> Value
       -> Check (Term 'Checked)

check' c (Let ctxt t) ty = do
  (ctxt', c') <- checkContext ctxt c
  t' <- check' c' t ty
  pure $ Let ctxt' t'

check' _ Type ty = case ty of
  VType -> pure Type
  _ -> throwError $ Mismatch Type ty

check' c (Var i) = undefined
--TODO: right here is where we need a "type context" or "type closure"
--  which would have some but not all overlap with the maybe-recursive type
--  environment

infer :: Term 'Unchecked -> Check (Term 'Checked, Term 'Checked)
infer = infer' []

infer' :: Closure -> Term 'Unchecked -> Check (Term 'Checked, Term 'Checked)
infer' = undefined

checkContext :: Context 'Unchecked
             -> Closure
             -> Check (Context 'Checked, Closure)
checkContext ctxt clos = go [] ctxt clos >>= checkUnique where
  go :: [(T.Text, RecBinding)]
     -> Context 'Unchecked
     -> Closure
     -> Check (Context 'Checked, Closure)

  go _ [] c = pure ([], c) -- TODO: all-defined check?

  go n ((Declare x ty):rest) c = do
    ty' <- check' c ty VType
    binding <- addBoundType (x, c, ty')
    (rest', c') <- go ((x, binding):n) rest (binding :- c)
    pure ((Declare x ty'):rest', c')

  go n ((Define x t):rest) c = do
    case lookup x n of
      Nothing -> throwError $ Undeclared x
      Just binding -> getBoundType binding >>= \case
        Nothing -> throwError $ Undeclared x -- shouldn't happen
        Just (_, cTy, ty) -> do
          ty' <- eval' cTy ty
          t' <- check' c t ty'
          updateBoundTerm binding (x, c, t')
          (rest', c') <- go n rest c
          pure ((Define x t'):rest', c')

checkUnique :: (Context 'Checked, Closure) -> Check (Context 'Checked, Closure)
checkUnique (ctxt, c) = go Set.empty Set.empty ctxt >> pure (ctxt, c) where
  go decls defns [] = case Set.lookupMin (Set.difference decls defns) of
    Nothing -> pure ()
    Just x -> throwError (Undefined x)
  go decls defns ((Declare x _):rest) = if Set.member x decls
    then throwError (DuplicateDeclare x)
    else go (Set.insert x decls) defns rest
  go decls defns ((Define x _):rest) = if Set.member x defns
    then throwError (DuplicateDefine x)
    else go decls (Set.insert x defns) rest

data TypedRecEnv = TypedRecEnv
  { getTypeEnv :: S.Seq (T.Text, Maybe (Closure, Term 'Checked))
  , getValueEnv :: S.Seq (T.Text, Maybe (Closure, Term 'Checked))
  , _nextBinding :: Int
  }

emptyTypedRecEnv :: TypedRecEnv
emptyTypedRecEnv = TypedRecEnv S.empty S.empty 0

newtype Check a = Check { getCheck :: ExceptT TypeError (State TypedRecEnv) a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError TypeError
           , MonadState TypedRecEnv
           )

instance MonadEval Check where
  getBoundTerm (MkRecBinding i) = do
    rec <- gets (S.lookup i . getValueEnv)
    pure $ do
      (x, val) <- rec
      (c, t) <- val
      pure $ (x, c, t)

  addBoundTerm (x, c, t) = do
    TypedRecEnv tyEnv tmEnv next <- get
    put $ TypedRecEnv
      (tyEnv S.:|> (x, Nothing)) (tmEnv S.:|> (x, Just (c, t))) (next + 1)
    pure $ MkRecBinding next

  updateBoundTerm (MkRecBinding i) (x, c, t) = do
    TypedRecEnv tyEnv tmEnv next <- get
    put $ TypedRecEnv tyEnv (S.update i (x, Just (c, t)) tmEnv) next

instance MonadCheck Check where
  getBoundType (MkRecBinding i) = do
    rec <- gets (S.lookup i . getTypeEnv)
    pure $ do
      (x, val) <- rec
      (c, t) <- val
      pure $ (x, c, t)

  addBoundType (x, c, ty) = do
    TypedRecEnv tyEnv tmEnv next <- get
    put $ TypedRecEnv
      (tyEnv S.:|> (x, Just (c, ty))) (tmEnv S.:|> (x, Nothing)) (next + 1)
    pure $ MkRecBinding next

runCheck :: Check a -> TypedRecEnv -> (Either TypeError a, TypedRecEnv)
runCheck = runState . runExceptT . getCheck

evalCheck :: Check a -> TypedRecEnv -> Either TypeError a
evalCheck = evalState . runExceptT . getCheck

execCheck :: Check a -> TypedRecEnv -> TypedRecEnv
execCheck = execState . runExceptT . getCheck
