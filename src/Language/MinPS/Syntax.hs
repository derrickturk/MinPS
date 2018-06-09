{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies #-}

module Language.MinPS.Syntax (
    TermState(..)
  , Stmt(..)
  , Context
  , Label(..)
  , Term(..)
) where

import qualified Data.Text as T

data TermState = Unchecked
               | Checked
               deriving Show

newtype Label = MkLabel { label :: T.Text }
  deriving (Show, Eq)

data Stmt :: TermState -> * where
  Declare :: T.Text -> Term s -> Stmt s
  Define :: T.Text -> Term s -> Stmt s

type Context s = [Stmt s]

data Term :: TermState -> * where
  Let :: Context s -> Term s -> Term s
  Type :: Term s
  Var :: Int -> Term s
  Pi :: T.Text -> Term s -> Term s -> Term s
  Sigma :: T.Text -> Term s -> Term s -> Term s
  Lam :: T.Text -> Term s -> Term s
  Pair :: Term s -> Term s -> Term s
  Enum :: [Label] -> Term s
  EnumLabel :: Label -> Term s
  Lift :: Term s -> Term s
  Box :: Term s -> Term s
  Rec :: Term s -> Term s
  Fold :: Term s -> Term s
  App :: Term s -> Term s -> Term s
  Split :: Term s -> T.Text -> T.Text -> Term s -> Term s
  Case :: Term s -> [(Label, Term s)] -> Term s
  Force :: Term s -> Term s
  Unfold :: Term s -> T.Text -> Term s -> Term s

deriving instance Show (Stmt 'Checked) 
deriving instance Show (Stmt 'Unchecked) 

deriving instance Show (Term 'Checked)
deriving instance Show (Term 'Unchecked)
