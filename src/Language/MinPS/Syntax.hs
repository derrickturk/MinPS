{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances, TypeFamilies, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Syntax (
    TermState(..)
  , Stmt(..)
  , Context
  , Label(..)
  , Ident(..)
  , Term(..)
) where

import Data.String
import qualified Data.Text as T

data TermState = Unchecked
               | Checked
               deriving Show

newtype Label = MkLabel { getLabel :: T.Text }
  deriving (Show, Eq, IsString)

newtype Ident = MkIdent { getIdent :: T.Text }
  deriving (Show, Eq, IsString)

data Stmt :: TermState -> * where
  Declare :: Ident -> Term s -> Stmt s
  Define :: Ident -> Term s -> Stmt s

type Context s = [Stmt s]

data Term :: TermState -> * where
  Let :: Context s -> Term s -> Term s
  Type :: Term s
  Var :: Ident -> Term s
  Pi :: Ident -> Term s -> Term s -> Term s
  Sigma :: Ident -> Term s -> Term s -> Term s
  Lam :: Ident -> Term s -> Term s
  Pair :: Term s -> Term s -> Term s
  Enum :: [Label] -> Term s
  EnumLabel :: Label -> Term s
  Lift :: Term s -> Term s
  Box :: Term s -> Term s
  Rec :: Term s -> Term s
  Fold :: Term s -> Term s
  App :: Term s -> Term s -> Term s
  Split :: Term s -> Ident -> Ident -> Term s -> Term s
  Case :: Term s -> [(Label, Term s)] -> Term s
  Force :: Term s -> Term s
  Unfold :: Term s -> Ident -> Term s -> Term s

deriving instance Show (Stmt 'Checked) 
deriving instance Show (Stmt 'Unchecked) 

deriving instance Show (Term 'Checked)
deriving instance Show (Term 'Unchecked)
