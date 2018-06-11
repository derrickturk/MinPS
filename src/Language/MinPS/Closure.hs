{-# LANGUAGE GADTs, KindSignatures #-}

module Language.MinPS.Closure (
    Scope
  , Closure(..)
) where

import Language.MinPS.Syntax

import Data.List (intercalate)
import qualified Data.Text as T

type Scope = [(Ident, Int)]

data Closure :: * -> * where
  (:@) :: a -> Scope -> Closure a
infix 4 :@

instance Show a => Show (Closure a) where
  show (x :@ []) = show x
  show (x :@ c) = show x ++ "[with " ++ intercalate ", " binds ++ "]" where
    binds = fmap (\(var, i) -> T.unpack (getIdent var) ++ "@" ++ show i) c
