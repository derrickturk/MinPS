{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}

module Language.MinPS.Compile (
    Compile(..)
) where

import qualified Data.Map as M

import Language.MinPS.Syntax
import Language.MinPS.Annotate
import Language.JS.Syntax

class Compile f a where
  compile :: f 'Annotated -> m a

instance Compile TermX JSExpr where
  compile = undefined

instance Compile Stmt JSStmt where
  compile = undefined
