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
  compile _ (AErased _) = JSUndefined

  compile c (ALet ctxt t) = JSCall (JSFun [] (letBody c ctxt t)) []

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
        isNull = JSBinOpApp JSEq t' JSNull
        discrim = case
          ( compile c (AEnumLabel repr null)
          , compile c (AEnumLabel repr nonNull)
          ) of
            (JSBool True, JSBool False) -> isNull
            (JSBool False, JSBool True) -> JSBinOpApp JSNEq t' JSNull
            (rNull, rNonNull) -> JSCond isNull rNull rNonNull
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
  compile c (APolyLam a (ALet ctxt t)) = go c [] a t where
    go c args AZ t = JSFun (reverse args) (letBody c ctxt t)
    go c args (AS x EKeep a) t = go ((jsVar x):c) ((jsIdent x):args) a t
    go c args (AS x (EErase _) a) t = go ((jsVar x):c) args a t
  compile c (APolyLam a t) = go c [] a t where
    go c args AZ t = JSLam (reverse args) (compile c t)
    go c args (AS x EKeep a) t = go ((jsVar x):c) ((jsIdent x):args) a t
    go c args (AS x (EErase _) a) t = go ((jsVar x):c) args a t

  compile c (ASatApp Saturated f args) =
    JSCall (compile c f) (compile c . snd <$> filter keep args)
  compile c (ASatApp (Unsaturated rest) f args) =
    let rest' = curriedNames (snd <$> filter keep rest) in
      JSLam rest'
        (JSCall (compile c f)
                ((compile c . snd <$> filter keep args) ++ (JSVar <$> rest')))

instance Compile StmtX ([JSExpr], [JSStmt]) where
  -- named function definitions will get hoisted, so we can skip the
  --   pre-declaration...
  compile c (ADeclare _ x (AErased EKTypeType)) = ((jsVar x):c, [])
  compile c (ADeclare _ x (AErased (EKPiType _))) = ((jsVar x):c, [])
  compile c (ADeclare FunctionalOrNone x _) =
    ((jsVar x):c, [JSLet (jsIdent x) Nothing])
  compile c (ADeclare DirectRec x _) =
    ((jsVar x):c, [JSLet (jsIdent x) (Just omega)])
  compile c (ADeclare BoxedRec x _) =
    ((jsVar x):c, [JSLet (jsIdent x) (Just $ JSArr [])])

  -- and just emit the definition
  compile c (ADefine _ _ (AErased _)) = (c, [])
  compile c (ADefine _ x (APolyLam a (ALet ctxt t))) =
    (c, go c [] a t) where
      go c args AZ t =
        [JSFunDef (jsIdent x) (reverse args) (letBody c ctxt t)]
      go c args (AS x EKeep a) t = go ((jsVar x):c) ((jsIdent x):args) a t
      go c args (AS x (EErase _) a) t = go ((jsVar x):c) args a t
  compile c (ADefine _ x (APolyLam a t)) =
    (c, go c [] a t) where
      go c args AZ t =
        [JSFunDef (jsIdent x) (reverse args) [JSReturn $ compile c t]]
      go c args (AS x EKeep a) t = go ((jsVar x):c) ((jsIdent x):args) a t
      go c args (AS x (EErase _) a) t = go ((jsVar x):c) args a t
  compile c (ADefine FunctionalOrNone x t) =
    (c, [JSExprStmt $ JSAssign (jsVar x) (compile c t)])
  compile c (ADefine DirectRec _ _) = (c, [])
  compile c (ADefine BoxedRec x t) =
    (c, [assignBoxedRec (jsVar x) (compile c t)])

  compile c (ADeclareDefine _ _ _ (AErased _)) = (c, [])
  compile c (ADeclareDefine _ x _ (APolyLam a (ALet ctxt t))) =
    ((jsVar x):c, go ((jsVar x):c) [] a t) where
      go c args AZ t =
        [JSFunDef (jsIdent x) (reverse args) (letBody c ctxt t)]
      go c args (AS x EKeep a) t = go ((jsVar x):c) ((jsIdent x):args) a t
      go c args (AS x (EErase _) a) t = go ((jsVar x):c) args a t
  compile c (ADeclareDefine _ x _ (APolyLam a t)) =
    ((jsVar x):c, go ((jsVar x):c) [] a t) where
      go c args AZ t =
        [JSFunDef (jsIdent x) (reverse args) [JSReturn $ compile c t]]
      go c args (AS x EKeep a) t = go ((jsVar x):c) ((jsIdent x):args) a t
      go c args (AS x (EErase _) a) t = go ((jsVar x):c) args a t
  compile c (ADeclareDefine FunctionalOrNone x _ t) =
    ((jsVar x):c, [JSLet (jsIdent x) (Just $ compile ((jsVar x):c) t)])
  compile c (ADeclareDefine DirectRec x _ _) =
    ((jsVar x):c, [JSLet (jsIdent x) (Just omega)])
  compile c (ADeclareDefine BoxedRec x _ t) =
    ((jsVar x):c, [ JSLet (jsIdent x) (Just $ JSArr [])
                  , assignBoxedRec (jsVar x) (compile ((jsVar x):c) t)
                  ])

compileProgram :: [AStmt] -> [JSStmt]
compileProgram = concat . go [] [] where 
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

keep :: (Erasure, a) -> Bool
keep (EKeep, _) = True
keep (EErase _, _) = False

letBody :: [JSExpr] -> [AStmt] -> ATerm -> [JSStmt]
letBody c ctxt t = concat (body c ctxt t) where
  body c (s:rest) t = let (c', s') = compile c s in s':(body c' rest t)
  body c [] t = [[JSReturn (compile c t)]]

curriedNames :: [Ident] -> [JSIdent]
curriedNames = go S.empty 1 where
  go :: S.Set Ident -> Integer -> [Ident] -> [JSIdent]
  go seen i (n:ns)
    | n == "_" = (newvar i):(go seen (i + 1) ns)
    | S.member n seen = (newvar i):(go seen (i + 1) ns)
    | otherwise = (MkJSIdent $ getIdent n):(go (S.insert n seen) i ns)
  go _ _ [] = []
  newvar = MkJSIdent . T.cons '$' . T.pack . show

omega :: JSExpr
omega = JSCall (JSFun [] [JSWhile (JSBool True) [JSEmptyStmt]]) []

assignBoxedRec :: JSExpr -> JSExpr -> JSStmt
assignBoxedRec dst src = JSExprStmt $
  JSCall (JSMember src "forEach")
         [JSFun ["$v", "$i"]
                [JSExprStmt $ JSAssign (JSIndex dst (JSVar "$i")) (JSVar "$v")]]
