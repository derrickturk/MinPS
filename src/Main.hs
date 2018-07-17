{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment
import System.FilePath
import System.IO
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Control.Monad.State.Strict
import Control.Monad.Except

import qualified Language.MinPS.Parse as P
import Language.MinPS.Check
import Language.MinPS.Environment
import Language.MinPS.Annotate
import Language.MinPS.Compile
import Language.MinPS.Pretty
import Language.JS.Syntax

import Language.MinPS.Repl

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> banner >> runRepl_ replLoop initialState
    _ -> mapM_ compileFile args

banner :: IO ()
banner = do
  putStrLn "    __      __     _       ____"
  putStrLn "   /  \\    /  \\   |_|     |  _ | __"
  putStrLn "  / /\\ \\  / /\\ \\   _  ___ |  __|| _|  by dwt"
  putStrLn " / /  \\ \\/ /  \\ \\ | ||`  || |   |_ |  terminus data science, LLC"
  putStrLn "/_/    \\__/    \\_\\|_||_|_||_|   |__|  (c) 2018"
  putStrLn ""

compileFile :: FilePath -> IO ()
compileFile path = do
  let outPath = dropExtension path <.> "js"
  src <- TIO.readFile path
  -- TODO: stuff (need prog/stmt parsers)
  let parsed = P.parse (P.space' *> P.only P.context) path src
  case parsed of
    Left err -> hPutStrLn stderr (P.parseErrorPretty err)
    Right prog -> case runState (runExceptT $ checkProgram prog) emptyE of 
      (Left err, _) -> do
        hPutStr stderr $ path ++ ": "
        TIO.hPutStrLn stderr (pretty err)
      (Right prog, env) -> let annotated = evalState (annotateProgram prog) env
                               compiled = compileProgram annotated in
                               TIO.writeFile outPath $
                                 T.intercalate "\n\n" $ fmap emit compiled
