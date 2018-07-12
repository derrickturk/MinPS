{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Pretty (
    Pretty(..)
) where

import qualified Data.Text as T
import Data.Monoid ((<>))

import Language.MinPS.Syntax
import Language.MinPS.Environment (Closure(..))
import Language.MinPS.Check

class Pretty a where
  pretty :: a -> T.Text

instance Pretty (Ident) where
  pretty = getIdent

instance Pretty (Label) where
  pretty = getLabel

instance Pretty (Stmt a) where
  pretty (Declare x ty) = pretty x <> ": " <> pretty ty <> ";\n"
  pretty (Define x t) = pretty x <> " = " <> pretty t <> ";\n"
  pretty (DeclareDefine x ty t) = pretty x <> ": " <> pretty ty
    <> " = " <> pretty t <> ";\n"

instance Pretty (TermX a) where
  pretty (Let _ ctxt t) = "let " <> foldMap pretty ctxt <> "in " <> pretty t
  pretty (Type _) = "Type"
  pretty (Var _ x) = pretty x
  pretty (Pi _ x ty t) = if x == "_"
    then pretty ty <> " -> " <> pretty t
    else "(" <> pretty x <> ": " <> pretty ty <> ") -> " <> pretty t
  pretty (Sigma _ x ty t) = if x == "_"
    then pretty ty <> " * " <> pretty t
    else "(" <> pretty x <> ": " <> pretty ty <> ") * " <> pretty t
  pretty (Lam _ x t) = "\\" <> pretty x <> " -> " <> pretty t
  pretty (Pair _ x y) = "(" <> pretty x <> ", " <> pretty y <> ")"
  pretty (Enum _ lbls) = "{" <> T.intercalate ", " (pretty <$> lbls) <> "}"
  pretty (EnumLabel _ l) = T.cons '\'' (pretty l)
  pretty (Lift _ t) = "^(" <> pretty t <> ")"
  pretty (Box _ t) = "[" <> pretty t <> "]"
  pretty (Rec _ t) = "Rec (" <> pretty t <> ")"
  pretty (Fold _ t) = "fold (" <> pretty t <> ")"
  pretty (App _ f t) = "(" <> pretty f <> ") (" <> pretty t <> ")"
  pretty (Split _ t x y u) = "split " <> pretty t <> " with ("
    <> pretty x <> ", " <> pretty y <> ") -> " <> pretty u
  pretty (Case _ t cases) = "case " <> pretty t <> " of {\n    "
   <> T.intercalate "\n  | " (prettyCase <$> cases) <> "\n}" where
     prettyCase (l, u) = pretty l <> " -> " <> pretty u
  pretty (Force _ t) = T.cons '!' (pretty t)
  pretty (Unfold _ t x u) = "unfold " <> pretty t <> " as " <> pretty x
    <> " -> " <> pretty u
  pretty (TermX _) = "<extension term>"

instance Pretty TypeError where
  pretty (Mismatch ex got) = "type mismatch:\n\texpected " <> pretty ex
    <> "\n\tgot " <> pretty got
  pretty (ExpectedGotLambda ex) = "got lambda; expected " <> pretty ex
  pretty (ExpectedGotPair ex) = "got pair; expected " <> pretty ex
  pretty (ExpectedGotLabel (MkLabel lbl) ex) = "got label '" <> lbl
    <> "; expected " <> pretty ex
  pretty (ExpectedPiType got) = "expected pi type; got " <> pretty got
  pretty (ExpectedSigmaType got) = "expected sigma type; got " <> pretty got
  pretty (ExpectedEnumType got) = "expected enum type; got " <> pretty got
  pretty (ExpectedLiftedType got) = "expected lifted type; got " <> pretty got
  pretty (ExpectedRecType got) = "expected Rec type; got " <> pretty got
  pretty (Undeclared (MkIdent x)) = "undeclared variable " <> x
  pretty (Undefined (MkIdent x)) = "undefined variable " <> x
  pretty (DuplicateDeclare (MkIdent x)) = "duplicate declarations for " <> x
  pretty (DuplicateDefine (MkIdent x)) = "duplicate definitions for " <> x
  pretty (DuplicateLabel (MkLabel l)) = "duplicate label " <> l
  pretty (LabelsMismatch ex got) = "labels mismatch; expected "
    <> pretty (UEnum ex :: UTerm)
    <> ", got " <> pretty (UEnum got :: UTerm)
  pretty (NotInferable (t :@ _)) = "not inferable: " <> pretty t
