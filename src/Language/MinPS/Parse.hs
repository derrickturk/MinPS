{-# LANGUAGE DataKinds, TupleSections, OverloadedStrings #-}

module Language.MinPS.Parse (
    Parser
  , ident
  , stmt
  , context
  , term
) where

import qualified Data.Text as T
import Text.Megaparsec hiding (label)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Void (Void)
import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NE

import Language.MinPS.Syntax

type Parser = Parsec Void T.Text

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: T.Text -> Parser T.Text
symbol = L.symbol space

enclosed :: T.Text -> T.Text -> Parser a -> Parser a
enclosed left right = between (symbol left) (symbol right)

keywords :: [T.Text]
keywords = [ "let"
           , "in"
           , "split"
           , "with"
           , "fold"
           , "unfold"
           , "as"
           , "Rec"
           , "Type"
           , "case"
           , "of"
           ]

ident :: Parser Ident
ident = lexeme $ do
  var <- T.pack <$> ((:) <$> letterChar <*> (many $ alphaNumChar <|> char '\''))
  if var `elem` keywords
    then failure
      (Just $ Label $ NE.fromList "keyword")
      (Set.singleton $ Label $ NE.fromList "identifier")
    else return $ MkIdent var

label :: Parser Label
label = lexeme $ (MkLabel . getIdent) <$> ident

labelTerm :: Parser Label
labelTerm = char '\'' *> label

-- TODO: the original allows syntax like (a b c d : Type)
-- but I don't think I've ever seen them use it, and I don't care for it
binder :: Parser (Ident, Term 'Unchecked)
binder = enclosed "(" ")" $ (,) <$> ident <*> (lexeme ":" *> term)

stmt :: Parser (Stmt 'Unchecked)
stmt =  try (Declare <$> ident <*> (lexeme ":" *> term <* lexeme ";"))
    <|> (Define <$> ident <*> (lexeme "=" *> term <* lexeme ";"))
    <?> "a declaration or definition"

context :: Parser (Context 'Unchecked)
context = some stmt

branch :: Parser (Label, Term 'Unchecked)
branch = (,) <$> label <*> (lexeme "->" *> term)

atom :: Parser (Term 'Unchecked)
atom =  try $ enclosed "(" ")" term
    <|> try (uncurry Pair <$>
          enclosed "(" ")" ((,) <$> term <*> (lexeme "," *> term)))
    <|> try (Enum <$> enclosed "{" "}" (some label))
    <|> try (EnumLabel <$> labelTerm)
    <|> try (Case <$> ("case" *> space1 *> term)
                  <*> ("of" *> enclosed "{" "}" (branch `sepBy` lexeme "|")))
    <|> try (Box <$> enclosed "[" "]" term)
    <|> Var <$> ident

prefix :: Parser (Term 'Unchecked -> Term 'Unchecked)
prefix =  try (Rec <$ lexeme "Rec")
      <|> try (Fold <$ lexeme "fold")
      <|> try (Lift <$ lexeme "^")
      <|> try (Force <$ lexeme "!")
      -- I am deliberately excluding prefix box operator Unicode sharp-sign
      <|> (\t -> Unfold t "x" (Var "x")) <$ lexeme "unfold"

appTerm :: Parser (Term 'Unchecked)
appTerm = foldl App <$> (atom <|> prefix <*> atom) <*> many atom

lambda :: Parser (Term 'Unchecked)
lambda = do
  lexeme $ char '\\'
  idents <- some ident
  lexeme $ string "->"
  body <- term
  pure $ foldr Lam body idents

productTerm :: Parser (Term 'Unchecked)
productTerm =  try (uncurry Sigma <$> binder <*> (lexeme "*" *> term))
           <|> (foldl $ Sigma "_") <$> appTerm <*> many productTerm

term :: Parser (Term 'Unchecked)
term =  try (Let <$> ("let" *> space1 *> context) <*> ("in" *> space1 *> term))
    <|> try lambda
    <|> try (Split <$> ("split" *> space1 *> term) <*>
                       (lexeme "with" *> lexeme "(" *> ident) <*>
                       (lexeme "," *> ident <* lexeme ")") <*>
                       (lexeme "->" *> term))
    <|> try (Unfold <$> ("unfold" *> space1 *> term) <*>
                        ("as" *> space1 *> ident) <*>
                        (lexeme "->" *> term))
    <|> try (uncurry Pi <$> binder <*> (lexeme "->" *> term)) 
    <|> (foldl $ Pi "_") <$> productTerm <*> many term
