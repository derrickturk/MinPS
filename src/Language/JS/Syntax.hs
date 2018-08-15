{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.JS.Syntax (
    JSIdent(..)
  , JSUnOp(..)
  , JSBinOp(..)
  , JSExpr(..)
  , JSStmt(..)
  , Emit(..)
) where

import Data.Monoid ((<>))
import Data.String (IsString)
import qualified Data.Text as T

newtype JSIdent = MkJSIdent { getJSIdent :: T.Text }
  deriving (Show, Eq, IsString, Ord)

data JSUnOp =
    JSNot
  | JSPreIncr
  | JSPreDecr
  | JSPostIncr
  | JSPostDecr
  deriving (Eq, Show)

data JSBinOp =
    JSEq
  | JSNEq
  | JSAnd
  | JSOr
  deriving (Eq, Show)

data JSExpr =
    JSInt Int
  | JSBool Bool
  | JSNull
  | JSUndefined
  | JSVar JSIdent
  | JSArr [JSExpr]
  | JSObj [(JSIdent, JSExpr)]
  | JSLam [JSIdent] JSExpr
  | JSFun [JSIdent] [JSStmt]
  | JSCond JSExpr JSExpr JSExpr 
  | JSCall JSExpr [JSExpr]
  | JSMember JSExpr JSIdent
  | JSIndex JSExpr JSExpr
  | JSUnOpApp JSUnOp JSExpr
  | JSBinOpApp JSBinOp JSExpr JSExpr
  | JSAssign JSExpr JSExpr
  | JSComma JSExpr JSExpr
  deriving (Eq, Show)

data JSStmt =
    JSEmptyStmt
  | JSLet JSIdent (Maybe JSExpr)
  | JSConst JSIdent JSExpr
  | JSReturn JSExpr
  | JSExprStmt JSExpr
  | JSFunDef JSIdent [JSIdent] [JSStmt]
  | JSIfElse JSExpr [JSStmt] (Maybe [JSStmt])
  | JSFor JSStmt JSExpr JSExpr [JSStmt]
  | JSWhile JSExpr [JSStmt]
  | JSSwitch JSExpr [(JSExpr, [JSStmt])]
  deriving (Eq, Show)

class Emit a where
  emit :: a -> T.Text
  emit = emit' 0 1

  -- outer and inner indent levels
  -- your inner becomes your inner stuff's outer
  emit' :: Int -> Int -> a -> T.Text
  emit' _ _ = emit

  {-# MINIMAL emit | emit' #-}

instance Emit JSExpr where
  emit' 0 _ (JSInt n) = T.pack $ show n
  emit' 0 _ (JSBool True) = "true"
  emit' 0 _ (JSBool False) = "false"
  emit' 0 _ JSNull = "null"
  emit' 0 _ JSUndefined = "undefined"
  emit' 0 _ (JSVar v) = getJSIdent v
  emit' o i (JSArr xs) = indent o <> "["
    <> sepMap ", " (emit' 0 i) xs <> "]"
  emit' o i (JSObj fields) = indent o <> "{ "
    <> sepMap ", " (emitField 0 i) fields <> " }"
    where emitField o i (f, x) = getJSIdent f <> ": " <> emit' o i x
  emit' o i (JSLam args res) = indent o <> "(" <> sepMap ", " getJSIdent args
    <> ") => " <> emit' 0 i res
  emit' o i (JSFun args body) = indent o <> "function ("
    <> sepMap ", " getJSIdent args <> ") {\n"
    <> sepMap "\n" (emit' i (i + 1)) body <> "\n"
    <> indent o <> "}"
  emit' o i (JSCond c t f) = "(" <> emit' o i c <> ") ? ("
    <> emit' o i t <> ") : (" <> emit' o i f <> ")"
  -- TODO: precedence
  emit' o i (JSCall f args) = indent o <> "("
    <> emit' 0 i f <> ")(" <> sepMap ", " (emit' 0 i) args <> ")"
  emit' o i (JSMember x m) = indent o <> "(" <> emit' 0 i x <> ")."
    <> getJSIdent m
  emit' o i (JSIndex x ix) = indent o <> "(" <> emit' 0 i x <> ")["
    <> emit' 0 i ix <> "]"
  emit' o i (JSUnOpApp op e) = indent o <> emitUnOp op (emit' 0 i e)
  emit' o i (JSBinOpApp op lhs rhs) = indent o <> "(" <> emit' 0 i lhs
    <> emitBinOp op <> emit' 0 i rhs <> ")"
  emit' o i (JSAssign lval rval) = indent o <> emit' 0 i lval <> " = "
    <> emit' 0 i rval
  emit' o i (JSComma t u) = indent o <> "(" <> emit' 0 i t <> "), ("
    <> emit' 0 i u <> ")"
  emit' o i e = indent o <> emit' 0 i e

instance Emit JSStmt where
  emit' 0 _ JSEmptyStmt = ";"
  emit' 0 _ (JSLet v Nothing) = "let " <> getJSIdent v <> ";"
  emit' 0 i (JSLet v (Just e)) = "let " <> getJSIdent v <> " = "
    <> emit' 0 i e <> ";"
  emit' 0 i (JSConst v e) = "const " <> getJSIdent v <> " = "
    <> emit' 0 i e <> ";"
  emit' 0 i (JSReturn e) = "return " <> emit' 0 i e <> ";"
  emit' o i (JSExprStmt e) = emit' o i e <> ";"
  emit' o i (JSFunDef name args body) = indent o <> "function "
    <> getJSIdent name <> "(" <> sepMap ", " getJSIdent args <> ") {\n"
    <> sepMap "\n" (emit' i (i + 1)) body <> "\n" <> indent o <> "}"
  emit' o i (JSIfElse cond ifBody elseBody) = indent o
    <> "if (" <> emit' 0 i cond <> ") {\n"
    <> sepMap "\n" (emit' i (i + 1)) ifBody
    <> "\n" <> indent o <> "}"
    <> case elseBody of
         Just body -> " else {\n"
           <> sepMap "\n" (emit' i (i + 1)) body
           <> "\n" <> indent o <> "}"
         Nothing -> ""
  emit' o i (JSFor init check update body) = indent o <> "for ("
    <> emit' 0 i init <> "; " <> emit' 0 i check <> "; " <> emit' 0 i update
    <> ") {\n" <> sepMap "\n" (emit' i (i + 1)) body
    <> "\n" <> indent o <> "}"
  emit' o i (JSWhile cond body) = indent o <> "while (" <> emit' 0 i cond
    <> ") {\n" <> sepMap "\n" (emit' i (i + 1)) body
    <> "\n" <> indent o <> "}"
  emit' o i (JSSwitch e cases) = indent o <> "switch (" <> emit e <> ") {\n"
    <> sepMap "\n" (emitCase i (i + 1)) cases
    <> "\n" <> indent o <> "}"
  emit' o i s = indent o <> emit' 0 i s

indent :: Int -> T.Text
indent n = T.replicate n "  "

sepMap :: T.Text -> (a -> T.Text) -> [a] -> T.Text
sepMap s f xs = T.intercalate s (f <$> xs)

emitUnOp :: JSUnOp -> T.Text -> T.Text
emitUnOp JSNot e = "!(" <> e <> ")"
emitUnOp JSPreIncr e = "++(" <> e <> ")"
emitUnOp JSPreDecr e = "--(" <> e <> ")"
emitUnOp JSPostIncr e = "(" <> e <> ")++"
emitUnOp JSPostDecr e = "(" <> e <> ")--"

emitBinOp :: JSBinOp -> T.Text
emitBinOp JSEq = " === "
emitBinOp JSNEq = " !== "
emitBinOp JSAnd = " && "
emitBinOp JSOr = " || "

emitCase :: Int -> Int -> (JSExpr, [JSStmt]) -> T.Text
emitCase o i (e, body) = indent o <> "case " <> emit' 0 i e <> ": \n"
  <> sepMap "\n" (emit' i (i + 1)) body
  <> "\n" <> indent i <> "break;\n"
