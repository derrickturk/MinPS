{-# LANGUAGE GADTs, DataKinds, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances, FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Compile (
    Compile(..)
  , compileProgram
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

  compile c (APair PairRepr t u) = JSArr [compile c t, compile c u]
  compile c (APair (NullableRepr null _) (AEnumLabel _ l) u)
    | l == null = JSNull
    | otherwise = JSArr [compile c u]
  compile c (APair (NullableRepr null repr) t u) = 
    JSCond (JSBinOpApp JSEq (compile c t) (compile c (AEnumLabel repr null)))
            JSNull
            (JSArr [(compile c u)])

  compile _ (AEnumLabel (_, reprs) l) = reprs M.! l

  compile c (ABox t) = JSLam [] (compile c t)

  -- TODO: hmmm
  compile c (AFold t) = compile c t

  -- TODO: we could introduce a temporary
  compile c (ASplit PairRepr t _ _ u) =
    let t' = compile c t
        c' = (JSIndex t' (JSInt 1)):(JSIndex t' (JSInt 0)):c in
        compile c' u
  compile c (ASplit (NullableRepr null repr) t _ _ u) =
    let t' = compile c t
        nonNull = case nonNullLabel repr null of
          Just l -> l
          _ -> error "internal error: invalid EnumRepr for NullableRepr"
        discrim = JSCond (JSBinOpApp JSEq t' JSNull)
                         (compile c (AEnumLabel repr null))
                         (compile c (AEnumLabel repr nonNull))
        c' = (JSIndex t' (JSInt 0)):discrim:c in
        compile c' u

  compile c (ACase (VoidRepr, _) t _) = JSComma (compile c t) JSUndefined
  compile c (ACase (UnitRepr, _) t [(_, u)]) =
    JSComma (compile c t) (compile c u)
  compile c (ACase (BoolRepr, reprs) t cases) = boolCases c t reprs cases
  compile c (ACase (IntRepr, reprs) t cases) = intCases c t reprs cases
  compile _ (ACase _ _ _) = error "internal error: invalid repr chosen"

  compile c (AForce t) = JSCall (compile c t) []

  compile c (AUnfold t x u) = case u of
    (Var 0 _) -> compile c t
    _ -> JSCall (JSLam [jsIdent x] (compile ((jsVar x):c) u)) [compile c t]

  -- TODO: handle shadowing etc etc
  compile c (APolyLam a t) = go c [] a t where
    go :: [JSExpr] -> [JSIdent] -> Arity -> ATerm -> JSExpr
    go c args AZ t = JSLam (reverse args) (compile c t)
    go c args (AS x a) t = go ((jsVar x):c) ((jsIdent x):args) a t

  compile c (ASatApp Saturated f args) =
    JSCall (compile c f) (compile c <$> args)
  compile c (ASatApp (Unsaturated rest) f args) =
    let rest' = curriedNames rest in
      JSLam rest'
        (JSCall (compile c f) ((compile c <$> args) ++ (JSVar <$> rest')))

  -- TODO: erasure (or handle in annotation)
  compile _ (AType) = JSUndefined
  compile _ (APi _ _ _ _) = JSUndefined
  compile _ (ASigma _ _ _ _) = JSUndefined
  compile _ (AEnum _ _) = JSUndefined
  compile _ (ARec _) = JSUndefined
  compile _ (ALift _) = JSUndefined

instance Compile Stmt ([JSExpr], JSStmt) where
  compile c (Declare x _) = ((jsVar x):c, JSLet (jsIdent x) Nothing)
  compile c (Define x t) = (c, JSExprStmt $ JSAssign (jsVar x) (compile c t))
  compile c (DeclareDefine x _ t) =
    ((jsVar x):c, JSLet (jsIdent x) (Just $ compile ((jsVar x):c) t))

compileProgram :: [Stmt 'Annotated] -> [JSStmt]
compileProgram = go [] [] where 
  go c p (s:rest) = let (c', s') = compile c s in go c' (s':p) rest
  go _ p [] = reverse p

jsVar :: Ident -> JSExpr
jsVar = JSVar . jsIdent

jsIdent :: Ident -> JSIdent
jsIdent = MkJSIdent . T.map fixChar . getIdent where
  fixChar '\'' = '$'
  fixChar c = c

boolCases :: [JSExpr] -> ATerm -> LabelMap -> [(Label, ATerm)] -> JSExpr
boolCases c t m [(l1, u1), (_, u2)] = case m M.! l1 of
  JSBool True -> JSCond (compile c t) (compile c u1) (compile c u2)
  _ -> JSCond (compile c t) (compile c u2) (compile c u1)
boolCases _ _ _ _ = error "internal error: invalid repr chosen"

intCases :: [JSExpr] -> ATerm -> LabelMap -> [(Label, ATerm)] -> JSExpr
intCases c t m cases =
  JSCall (JSFun ["$arg"] [ JSLet "$result" Nothing
                         , JSSwitch (JSVar "$arg") (fmap setCase cases)
                         , JSReturn (JSVar "$result")
                         ])
         [(compile c t)]
  where
    setCase (l, t) =
      (m M.! l, [JSExprStmt $ JSAssign (JSVar "$result") (compile c t)])

curriedNames :: [Ident] -> [JSIdent]
curriedNames = go S.empty 1 where
  go :: S.Set Ident -> Integer -> [Ident] -> [JSIdent]
  go seen i (n:ns)
    | n == "_" = (newvar i):(go seen (i + 1) ns)
    | S.member n seen = (newvar i):(go seen (i + 1) ns)
    | otherwise = (MkJSIdent $ getIdent n):(go (S.insert n seen) i ns)
  go _ _ [] = []
  newvar = MkJSIdent . T.cons '$' . T.pack . show
