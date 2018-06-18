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

instance Pretty (Term a) where
  pretty (Let ctxt t) = "let " <> foldMap pretty ctxt <> "in " <> pretty t
  pretty (Type) = "Type"
  pretty (Var x) = pretty x
  pretty (Pi x ty t) = if x == "_"
    then pretty ty <> " -> " <> pretty t
    else "(" <> pretty x <> ": " <> pretty ty <> ") -> " <> pretty t
  pretty (Sigma x ty t) = if x == "_"
    then pretty ty <> " * " <> pretty t
    else "(" <> pretty x <> ": " <> pretty ty <> ") * " <> pretty t
  pretty (Lam x t) = "\\" <> pretty x <> " -> " <> pretty t
  pretty (Pair x y) = "(" <> pretty x <> ", " <> pretty y <> ")"
  pretty (Enum lbls) = "{" <> T.intercalate ", " (pretty <$> lbls) <> "}"
  pretty (EnumLabel l) = T.cons '\'' (pretty l)
  pretty (Lift t) = "^(" <> pretty t <> ")"
  pretty (Box t) = "[" <> pretty t <> "]"
  pretty (Rec t) = "Rec (" <> pretty t <> ")"
  pretty (Fold t) = "fold (" <> pretty t <> ")"
  pretty (App f t) = "(" <> pretty f <> ") (" <> pretty t <> ")"
  pretty (Split t x y u) = "split " <> pretty t <> " with ("
    <> pretty x <> ", " <> pretty y <> ") -> " <> pretty u
  pretty (Case t cases) = "case " <> pretty t <> " of {\n    "
   <> T.intercalate "\n  | " (prettyCase <$> cases) <> "\n}" where
     prettyCase (l, u) = pretty l <> " -> " <> pretty u
  pretty (Force t) = T.cons '!' (pretty t)
  pretty (Unfold t x u) = "unfold " <> pretty t <> " as " <> pretty x
    <> " -> " <> pretty u

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
    <> pretty (Enum ex)
    <> ", got " <> pretty (Enum got)
  pretty (NotInferable (t :@ _)) = "not inferable: " <> pretty t
