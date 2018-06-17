{-# LANGUAGE GADTs, KindSignatures, DataKinds, TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Repl (
    ReplState(..)
  , Repl
  , initialState
  , runRepl
  , evalRepl
  , execRepl
  , runRepl_
  , replTypecheckStmt
  , replTypecheckTerm
  , replExecStmt
  , replEvalTerm
  , replLine
  , replLoop
  , replPutStr
  , replPutStrLn
  , replPrint
  , replPrompt
  , replLoad
  , replClear
) where

import Control.Monad.State.Strict
import Control.Monad.Except

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as Set

import System.IO (hFlush, stdout)
import System.IO.Error (isEOFError, catchIOError, ioError)
import System.Exit (exitSuccess)

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Check
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.MinPS.Normalize
import qualified Language.MinPS.Parse as P

data ReplState = ReplState { replScope :: Scope
                           , replEnv :: Env
                           , replDecls :: Set.Set Ident
                           , replDefns :: Set.Set Ident
                           } deriving Show

newtype Repl a = Repl { getRepl :: ExceptT TypeError (StateT ReplState IO) a }
  deriving (
      Functor
    , Applicative
    , Monad
    , MonadError TypeError
    , MonadState ReplState
    , MonadIO
  )

initialState :: ReplState
initialState = ReplState emptyS emptyE Set.empty Set.empty

runRepl :: Repl a -> ReplState -> IO (Either TypeError a, ReplState)
runRepl (Repl r) s = runStateT (runExceptT r) s

evalRepl :: Repl a -> ReplState -> IO (Either TypeError a)
evalRepl (Repl r) s = evalStateT (runExceptT r) s

execRepl :: Repl a -> ReplState -> IO ReplState
execRepl (Repl r) s = execStateT (runExceptT r) s

runRepl_ :: Repl a -> ReplState -> IO ()
runRepl_ (Repl r) s = () <$ runStateT (runExceptT r) s

updateScope :: Scope -> Repl ()
updateScope s = modify (\r -> r { replScope = s })

updateEnv :: Env -> Repl ()
updateEnv e = modify (\r -> r { replEnv = e })

replTypecheckStmt :: Stmt 'Unchecked -> Repl (Stmt 'Checked)
replTypecheckStmt stmt = Repl $ do
  ReplState c env decls defns <- get
  case runState (runExceptT $ checkStmt (stmt :@ c) decls defns) env of
    (Right (stmt' :@ c', decls', defns'), env') -> do
      put $ ReplState c' env' decls' defns'
      pure stmt'
    (Left e, _) -> throwError e

replTypecheckTerm :: Term 'Unchecked
                  -> Repl (Closure (Term 'Checked), Term 'Checked)
replTypecheckTerm term = Repl $ do
  env <- gets replEnv
  c <- gets replScope
  case runState (runExceptT $ infer (term :@ c)) env of
    (Right (ty, term'), env') -> do
      getRepl $ updateEnv env'
      pure (ty, term')
    (Left e, _) -> throwError e

replExecStmt :: Stmt 'Checked -> Repl ()
replExecStmt stmt = do
  env <- gets replEnv
  c <- gets replScope
  let (c', env') = runState (evalStmt stmt c) env
  updateScope c'
  updateEnv env'

replEvalTerm :: Term 'Checked -> Repl Value
replEvalTerm term = do
  env <- gets replEnv
  c <- gets replScope
  let (v, env') = runState (eval' (term :@ c)) env
  updateEnv env'
  pure v

replNormalizeTerm :: Term 'Checked -> Repl (Term 'Checked)
replNormalizeTerm term = do
  v <- replEvalTerm term
  env <- gets replEnv
  let (n, env') = runState (normalize v) env
  updateEnv env'
  pure n

replPutStr :: String -> Repl ()
replPutStr = liftIO . putStr

replPutStrLn :: String -> Repl ()
replPutStrLn = liftIO . putStrLn

replPrint :: Show a => a -> Repl ()
replPrint = liftIO . print

replPrompt :: Repl ()
replPrompt = do
  replPutStrLn ""
  replPutStr "MinPS> "
  liftIO (hFlush stdout)

replLine :: Repl ()
replLine = do
  replPrompt
  line <- liftIO $ TIO.getLine `catchIOError` handler
  let parsed = P.parse (P.only P.replCommand) "stdin" line
  case parsed of
    Left err -> do
      replPutStrLn $ P.parseErrorPretty err
    Right (ReplEval term) -> do
      do
        (_, term') <- replTypecheckTerm term
        n <- replNormalizeTerm term'
        replPrint n
      `catchError` replPrint
    Right (ReplExec stmt) -> do
      do
        stmt' <- replTypecheckStmt stmt
        replExecStmt stmt'
      `catchError` replPrint
    Right (ReplCmd c arg) -> case lookup c replCmds of
      Just cmd -> cmd arg `catchError` replPrint
      Nothing -> do
        replPutStrLn $ "unknown repl command: :" ++ T.unpack c
  where
    handler e = if isEOFError e
      then exitSuccess
      else ioError e

replLoad :: Maybe T.Text -> Repl ()
replLoad Nothing = replPutStrLn "Usage: :load filename"
replLoad (Just file) = do
  let file' = T.unpack file
  src <- liftIO $ (Just <$> TIO.readFile file') `catchError` handler
  case src of
    Just src' -> do
      let parsed = P.parse (P.only P.context) file' src'
      case parsed of
        Left err -> replPutStrLn $ P.parseErrorPretty err
        Right ctxt -> do
          ctxt' <- mapM replTypecheckStmt ctxt
          mapM_ replExecStmt ctxt'
    Nothing -> replPutStrLn "Unable to load file."
  where
    handler _ = pure Nothing

replClear :: Repl ()
replClear = put initialState

replLoop :: Repl ()
replLoop = replLine >> replLoop

replCmds :: [(T.Text, Maybe T.Text -> Repl())]
replCmds = [ ("quit", const quit)
           , ("q", const quit)
           , ("load", replLoad)
           , ("l", replLoad)
           , ("clear", const replClear)
           , ("c", const replClear)
           ] where
  quit = replPutStrLn "" >> liftIO exitSuccess
