{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Compile (
    Compile(..)
  , jsVar
  , jsIdent
) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T

import Language.MinPS.Syntax
import Language.MinPS.Annotate
import Language.JS.Syntax

class Compile f a | f -> a where
  compile :: [JSExpr] -> f 'Annotated -> a

instance Compile TermX JSExpr where
  compile c (ALet ctxt t) = JSCall (JSFun [] (body c ctxt t)) [] where
    body c (s:rest) t = let (c', s') = compile c s in s':(body c' rest t)
    body c [] t = [JSReturn (compile c t)]

  compile c (AVar i _) = c !! i

  compile c (APair t u) = JSArr [compile c t, compile c u]

  compile _ (AEnumLabel (_, reprs) l) = reprs M.! l

  compile c (ABox t) = JSLam [] (compile c t)

  -- TODO: hmmm
  compile c (AFold t) = compile c t

  -- TODO: we could introduce a temporary
  compile c (ASplit t _ _ u) =
    let t' = compile c t
        c' = (JSIndex t' (JSInt 1)):(JSIndex t' (JSInt 0)):c in
        compile c' u

  -- TODO: erasure (or handle in annotation)
  compile _ (AType) = JSNull
  compile _ (APi _ _ _ _) = JSNull
  compile _ (ASigma _ _ _ _) = JSNull
  compile _ (AEnum _ _) = JSNull
  compile _ (ARec _) = JSNull
  compile _ (ALift _) = JSNull

  compile _ _ = JSUndefined

instance Compile Stmt ([JSExpr], JSStmt) where
  compile c (Declare x _) = ((jsVar x):c, JSLet (jsIdent x) Nothing)
  compile c (Define x t) = (c, JSExprStmt $ JSAssign (jsVar x) (compile c t))
  compile c (DeclareDefine x _ t) =
    ((jsVar x):c, JSLet (jsIdent x) (Just $ compile ((jsVar x):c) t))

jsVar :: Ident -> JSExpr
jsVar = JSVar . jsIdent

jsIdent :: Ident -> JSIdent
jsIdent = MkJSIdent . getIdent

curriedNames :: [Ident] -> [JSIdent]
curriedNames = go S.empty 1 where
  go :: S.Set Ident -> Integer -> [Ident] -> [JSIdent]
  go seen i (n:ns)
    | n == "_" = (newvar i):(go seen (i + 1) ns)
    | S.member n seen = (newvar i):(go seen (i + 1) ns)
    | otherwise = (MkJSIdent $ getIdent n):(go (S.insert n seen) i ns)
  go _ _ [] = []
  newvar = MkJSIdent . T.cons '$' . T.pack . show