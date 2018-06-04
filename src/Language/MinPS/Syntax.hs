{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}

module Language.MinPS.Syntax (
    TermState(..)
  , Label(..)
  , Term(..)
) where

import qualified Data.Text as T

data TermState = Unchecked
               | Checked
               deriving Show

newtype Label = MkLabel { label :: T.Text }
  deriving (Show, Eq)

data Term :: TermState -> * where
  Type :: Term s
  Var :: Int -> Term s
  Pi :: T.Text -> Term s -> Term s -> Term s
  Sigma :: T.Text -> Term s -> Term s -> Term s
  Lam :: T.Text -> Term s
  Pair :: Term s -> Term s -> Term s
  Enum :: [Label] -> Term s
  EnumLabel :: Label -> Term s
  Lift :: Term s -> Term s
  Box :: Term s -> Term s
  Rec :: Term s -> Term s
  Fold :: Term s -> Term s
  App :: Term s -> Term s -> Term s
  Split :: Term s -> T.Text -> T.Text -> Term s
  Case :: Term s -> [(Label, Term s)] -> Term s
  Force :: Term s -> Term s
  Unfold :: Term s -> T.Text -> Term s

deriving instance Show (Term s)
