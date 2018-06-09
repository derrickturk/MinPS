{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Check (
    TypeError
  , TypedRecEnv
  , emptyTypedRecEnv
  , Check
  , runCheck
  , evalCheck
  , execCheck
  , check
  , infer
) where

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Eval

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Sequence as S
import qualified Data.Text as T

-- we're going to use the Closure structure to store the types
--   (as WHNF forms) of bound values during checking in addition
--   to their values as in Eval
-- we'll adapt the RecEnv idea and track two environments, the environment
--   of values and the environment of types, for possibly
--   mutually-recursive bindings

data TypeError =
    Mismatch (Term 'Checked) (Term 'Checked)
  deriving Show

data TypedRecEnv = TypedRecEnv
  { getTypeEnv :: S.Seq (T.Text, Closure, Term 'Checked)
  , getValueEnv :: S.Seq (T.Text, Closure, Term 'Checked)
  , nextBinding :: Int
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
runCheck :: Check a -> TypedRecEnv -> (Either TypeError a, TypedRecEnv)
runCheck = runState . runExceptT . getCheck

evalCheck :: Check a -> TypedRecEnv -> Either TypeError a
evalCheck = evalState . runExceptT . getCheck

execCheck :: Check a -> TypedRecEnv -> TypedRecEnv
execCheck = execState . runExceptT . getCheck

{-- not convinced this can work; not convinced it needs to
liftEval :: Eval a -> Check a
liftEval m = do
  TypedRecEnv tyE valE next <- get
  let (x, RecEnv valE' next') = runEval m (RecEnv valE next)
  put $ TypedRecEnv tyE valE' next'
  pure x
--}

check :: Term 'Unchecked -> Term 'Checked -> Check (Term 'Checked)
check = check' []

check' :: Closure
       -> Term 'Unchecked
       -> Term 'Checked
       -> Check (Term 'Checked)
check' c (Let ctxt t) ty = do
  (ctxt', c') <- checkContext ctxt c
  t' <- check' c' t ty
  pure $ Let ctxt' t'

infer :: Term 'Unchecked -> Check (Term 'Checked, Term 'Checked)
infer = infer' []

infer' :: Closure -> Term 'Unchecked -> Check (Term 'Checked, Term 'Checked)
infer' = undefined

checkContext :: Context 'Unchecked
             -> Closure
             -> Check (Context 'Checked, Closure)
checkContext = go [] where
  go :: [(T.Text, Int)]
     -> Context 'Unchecked
     -> Closure
     -> Check (Context 'Checked, Closure)

  go _ [] c = pure ([], c)

  go n ((Declare x ty):rest) c = do
    next <- gets nextBinding
    env <- gets getTypeEnv
    -- let c' = MkLabel
    undefined -- TODO

  go n ((Define x t):rest) c = go n rest c -- TODO fix
