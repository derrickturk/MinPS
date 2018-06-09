{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Check (
    check
  , infer
) where

import Language.MinPS.Syntax
import Language.MinPS.Value
import Language.MinPS.Eval

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Sequence as S
import qualified Data.Text as T

data TypeError =
    Mismatch (Term 'Checked) (Term 'Checked)
  deriving Show

type TypeClosure = [Either RecBinding (Term 'Checked)]

newtype Check a = Check { getCheck :: ExceptT TypeError (State RecEnv) a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError TypeError
           , MonadState RecEnv
           )

evalCheck :: Eval a -> Check a
evalCheck m = do
  env <- get
  let (x, env') = runEval m env
  put env'
  pure x

check :: Term 'Unchecked -> Term 'Checked -> Check (Term 'Checked)
check = check' []

check' :: TypeClosure
       -> Term 'Unchecked
       -> Term 'Checked
       -> Check (Term 'Checked)
check' = undefined
-- check' c (Let ctxt t) ty = do

infer :: Term 'Unchecked -> Check (Term 'Checked, Term 'Checked)
infer = infer' []

infer' :: TypeClosure -> Term 'Unchecked -> Check (Term 'Checked, Term 'Checked)
infer' = undefined

{--
checkContext :: Context 'Unchecked
             -> TypeClosure
             -> Check (TypeClosure, Context 'Checked)
checkContext [] c = pure (c, [])
checkContext ((x, ty, t):rest)
--}
