{-# LANGUAGE DataKinds, TupleSections, OverloadedStrings #-}

module Language.MinPS.Parse (
    Parser
  , space'
  , ident
  , stmt
  , context
  , term
  , replCommand
  , parse
  , parseMaybe
  , parseTest
  , parseTest'
  , runParser
  , runParser'
  , parseErrorPretty
  , only
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

space' :: Parser ()
space' = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space'

symbol :: T.Text -> Parser T.Text
symbol = L.symbol space'

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
binder :: Parser (Ident, UTerm)
binder = enclosed "(" ")" $ (,) <$> ident <*> (lexeme ":" *> term)

stmt :: Parser (Stmt 'Unchecked)
stmt =  try (Declare <$> ident <*> (lexeme ":" *> term <* lexeme ";"))
    <|> try (Define <$> ident <*> (lexeme "=" *> term <* lexeme ";"))
    <|> (DeclareDefine <$> ident
                       <*> (lexeme ":" *> term)
                       <*> (lexeme "=" *> term <* lexeme ";"))
    <?> "a declaration or definition"

context :: Parser (Context 'Unchecked)
context = some stmt

branch :: Parser (Label, UTerm)
branch = (,) <$> label <*> (lexeme "->" *> term)

atom :: Parser (UTerm)
atom =  try (enclosed "(" ")" term)
    <|> try (uncurry UPair <$>
          enclosed "(" ")" ((,) <$> term <*> (lexeme "," *> term)))
    <|> try (UEnum <$> enclosed "{" "}" (many label))
    <|> try (UEnumLabel <$> labelTerm)
    <|> try (UCase <$> ("case" *> space1 *> term)
                  <*> (lexeme "of" *>
                       enclosed "{" "}" (branch `sepBy` lexeme "|")))
    <|> try (UBox <$> enclosed "[" "]" term)
    <|> try (UType <$ lexeme "Type")
    <|> try (UVar <$> ident)

prefix :: Parser (UTerm -> UTerm)
prefix =  try (URec <$ lexeme "Rec")
      <|> try (UFold <$ lexeme "fold")
      <|> try (ULift <$ lexeme "^")
      <|> try (UForce <$ lexeme "!")
      -- I am deliberately excluding prefix box operator Unicode sharp-sign
      <|> (\t -> UUnfold t "x" (UVar "x")) <$ lexeme "unfold"

appTerm :: Parser (UTerm)
appTerm = foldl UApp <$> (atom <|> prefix <*> atom) <*> many atom

lambda :: Parser (UTerm)
lambda = do
  lexeme $ char '\\'
  idents <- some ident
  lexeme $ string "->"
  body <- term
  pure $ foldr ULam body idents

productTerm :: Parser (UTerm)
productTerm =  try (uncurry USigma <$> binder <*> (lexeme "*" *> term))
           <|> (foldl $ USigma "_") <$> appTerm
                                   <*> many (lexeme "*" *> productTerm)

-- TODO: recognize the "original" let syntax again
term :: Parser (UTerm)
term =  try (ULet <$> (lexeme "let" *> lexeme "{" *> context <* lexeme "}")
                  <*> ("in" *> space1 *> term))
    <|> try lambda
    <|> try (USplit <$> ("split" *> space1 *> term) <*>
                       (lexeme "with" *> lexeme "(" *> ident) <*>
                       (lexeme "," *> ident <* lexeme ")") <*>
                       (lexeme "->" *> term))
    <|> try (UUnfold <$> ("unfold" *> space1 *> term) <*>
                        ("as" *> space1 *> ident) <*>
                        (lexeme "->" *> term))
    <|> try (uncurry UPi <$> binder <*> (lexeme "->" *> term)) 
    <|> (foldl $ UPi "_") <$> productTerm <*> many (lexeme "->" *> term)

replCommand :: Parser ReplCommand
replCommand =  try ((ReplCmd . T.pack) <$> lexeme (char ':' *> some letterChar)
                                       <*> optional (T.pack <$> some anyChar))
           <|> try (ReplExec <$> stmt)
           <|> (ReplEval <$> term)

only :: Parser a -> Parser a
only = (<* lexeme eof)
