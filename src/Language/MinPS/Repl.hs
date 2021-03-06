{-# LANGUAGE GADTs, KindSignatures, DataKinds, TypeOperators #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.MinPS.Repl (
    ReplState(..)
  , ReplSettings(..)
  , Repl
  , initialState
  , initialSettings
  , runRepl
  , evalRepl
  , execRepl
  , runRepl_
  , replTypecheckStmt
  , replTypecheckTerm
  , replExecStmt
  , replEvalClosure
  , replNormalizeClosure
  , replEvalTerm
  , replNormalizeTerm
  , replAnnotate
  , replCompile
  , replCompileFile
  , replLine
  , replLoop
  , replPutStr
  , replPutStrLn
  , replPutText
  , replPutTextLn
  , replPrint
  , replPrompt
  , replLoad
  , replClear
) where

import Control.Monad.State.Strict
import Control.Monad.Except

import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Set as S
import qualified Data.Map.Strict as M

import System.IO (hFlush, stdout)
import System.IO.Error (isEOFError, catchIOError, ioError)
import System.Exit (exitSuccess)

import Data.Fuel
import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Check
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.MinPS.Normalize
import Language.MinPS.Pretty
import Language.MinPS.Annotate
import Language.MinPS.Compile
import Language.JS.Syntax
import qualified Language.MinPS.Parse as P

data ReplState = ReplState { replScope :: Scope
                           , replEnv :: Env
                           , replDecls :: S.Set Ident
                           , replDefns :: S.Set Ident
                           , replSettings :: ReplSettings
                           , replFreeVars :: M.Map Ident FreeVariableMap
                           } deriving Show

data ReplSettings = ReplSettings { showTypes :: Bool
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

initialSettings :: ReplSettings
initialSettings = ReplSettings False

initialState :: ReplState
initialState = ReplState emptyS emptyE S.empty S.empty initialSettings M.empty

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

updateSettings :: ReplSettings -> Repl ()
updateSettings s = modify (\r -> r { replSettings = s })

addFreeVars :: Ident -> FreeVariableMap -> Repl ()
addFreeVars x frees = modify
  (\r -> r { replFreeVars = M.insert x frees (replFreeVars r) })

replTypecheckStmt :: UStmt -> Repl (KStmt)
replTypecheckStmt stmt = Repl $ do
  ReplState c env decls defns settings frees <- get
  case runState (runExceptT $ checkStmt (stmt :@ c) decls defns) env of
    (Right (stmt' :@ c', decls', defns'), env') -> do
      put $ ReplState c' env' decls' defns' settings frees
      pure stmt'
    (Left e, _) -> throwError e

replTypecheckTerm :: UTerm -> Repl KTerm
replTypecheckTerm term = Repl $ do
  env <- gets replEnv
  c <- gets replScope
  case runState (runExceptT $ infer (term :@ c)) env of
    (Right term', env') -> do
      getRepl $ updateEnv env'
      pure term'
    (Left e, _) -> throwError e

replExecStmt :: KStmt -> Repl ()
replExecStmt stmt = do
  env <- gets replEnv
  c <- gets replScope
  let (c', env') = runState (evalStmt (forget stmt) c) env
  updateScope c'
  updateEnv env'
  case stmt of
    KDeclare _ _ -> pure ()
    KDefine x t -> do
      let f = evalState (free t) env'
      addFreeVars x f
    KDeclareDefine x _ t -> do
      let f = evalState (free t) env'
      addFreeVars x f

replEvalClosure :: Closure CTerm -> Repl Value
replEvalClosure termC = do
  env <- gets replEnv
  let (v, env') = runState (eval' termC) env
  updateEnv env'
  pure v

replNormalizeClosure :: Closure CTerm -> Repl (CTerm)
replNormalizeClosure termC = do
  v <- replEvalClosure termC
  env <- gets replEnv
  let (n, env') = runState (normalize v) env
  updateEnv env'
  pure n

replEvalTerm :: CTerm -> Repl Value
replEvalTerm term = do
  c <- gets replScope
  replEvalClosure (term :@ c)

replNormalizeTerm :: CTerm -> Repl (CTerm)
replNormalizeTerm term = do
  c <- gets replScope
  replNormalizeClosure (term :@ c)

replAnnotate :: Maybe T.Text -> Repl ()
replAnnotate Nothing = replPutTextLn "Usage: :annotate stmt-or-term"
replAnnotate (Just line) = case P.parse (P.only P.stmt) "stdin" line of
  Left _ -> case P.parse (P.only P.term) "stdin" line of
    Left err -> replPutStrLn $ P.parseErrorPretty err
    Right t -> locally $ do
      t' <- replTypecheckTerm t
      names <- gets (fmap fst . replScope)
      env <- gets replEnv
      let t'' = evalState (annotate' names t') env
      replPrint t''
  Right s -> locally $ do
    s' <- replTypecheckStmt s
    names <- gets (fmap fst . replScope)
    env <- gets replEnv
    frees <- gets replFreeVars
    let (_, _, s'') = evalState (annotateStmt frees names s') env
    replPrint s''

replCompile :: Maybe T.Text -> Repl ()
replCompile Nothing = replPutTextLn "Usage: :compile stmt-or-term"
replCompile (Just line) = case P.parse (P.only P.stmt) "stdin" line of
  Left _ -> case P.parse (P.only P.term) "stdin" line of
    Left err -> replPutStrLn $ P.parseErrorPretty err
    Right t -> locally $ do
      t' <- replTypecheckTerm t
      names <- gets (fmap fst . replScope)
      env <- gets replEnv
      let t'' = evalState (annotate' names t') env
      replPutTextLn $ emit $ compile (jsVar <$> names) t''
  Right s -> locally $ do
    s' <- replTypecheckStmt s
    names <- gets (fmap fst . replScope)
    env <- gets replEnv
    frees <- gets replFreeVars
    let (_, _, s'') = evalState (annotateStmt frees names s') env
    let (_, js) = compile (jsVar <$> names) s''
    mapM_ (replPutTextLn . emit) js

replCompileFile :: Maybe T.Text -> Repl ()
replCompileFile Nothing = replPutStrLn "Usage: :compilefile filename"
replCompileFile (Just file) = do
  let file' = T.unpack file
  src <- liftIO $ (Just <$> TIO.readFile file') `catchError` handler
  case src of
    Just src' -> do
      let parsed = P.parse (P.only P.context) file' src'
      case parsed of
        Left err -> replPutStrLn $ P.parseErrorPretty err
        Right ctxt -> locally $ do
          ctxt' <- mapM replTypecheckStmt ctxt
          env <- gets replEnv
          let ctxt'' = evalState (annotateProgram ctxt') env
              compiled = compileProgram ctxt''
          mapM_ (replPutTextLn . emit) compiled
        `catchError` replHandleTypeError
    Nothing -> replPutStrLn "Unable to load file."
  where
    handler _ = pure Nothing

replPutStr :: String -> Repl ()
replPutStr = liftIO . putStr

replPutStrLn :: String -> Repl ()
replPutStrLn = liftIO . putStrLn

replPutText :: T.Text -> Repl ()
replPutText = liftIO . TIO.putStr

replPutTextLn :: T.Text -> Repl ()
replPutTextLn = liftIO . TIO.putStrLn

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
        term' <- replTypecheckTerm term
        n <- replNormalizeTerm (forget term')
        replPutTextLn $ pretty n

        showTy <- gets (showTypes . replSettings)
        when showTy $ do
          nTy <- replNormalizeClosure (typeOf term')
          replPutText " : "
          replPutTextLn $ pretty nTy
      `catchError` replHandleTypeError
    Right (ReplExec stmt) -> do
      do
        stmt' <- replTypecheckStmt stmt
        replExecStmt stmt'
      `catchError` replHandleTypeError
    Right (ReplCmd c arg) -> case lookup c replCmds of
      Just cmd -> cmd arg `catchError` replHandleTypeError
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
        `catchError` replHandleTypeError
    Nothing -> replPutStrLn "Unable to load file."
  where
    handler _ = pure Nothing

replHandleTypeError :: TypeError -> Repl ()
replHandleTypeError = replPutTextLn . pretty

replClear :: Repl ()
replClear = do
  f <- gets (getFuel . replEnv)
  put $ initialState { replEnv = setFuel f emptyE }

replLoop :: Repl ()
replLoop = replLine >> replLoop

replCmds :: [(T.Text, Maybe T.Text -> Repl())]
replCmds = [ ("quit", const quit)
           , ("q", const quit)
           , ("load", replLoad)
           , ("l", replLoad)
           , ("clear", const replClear)
           , ("c", const replClear)
           , ("fuel", replSetFuel)
           , ("f", replSetFuel)
           , ("showtypes", replSetShowTypes True)
           , ("st", replSetShowTypes True)
           , ("noshowtypes", replSetShowTypes False)
           , ("nst", replSetShowTypes False)
           , ("annotate", replAnnotate)
           , ("a", replAnnotate)
           , ("compile", replCompile)
           , ("co", replCompile)
           , ("compilefile", replCompileFile)
           , ("cf", replCompileFile)
           ] where
  quit = replPutStrLn "" >> liftIO exitSuccess
  replSetFuel (Just t)
    | t == "infinite" = do
        env <- gets replEnv
        updateEnv (setFuel infiniteFuel env)
    | [(n, "")] <- reads (T.unpack t) = do
        env <- gets replEnv
        updateEnv (setFuel (fuel n) env)
  replSetFuel _ = replPutStrLn "Usage: :fuel count"
  replSetShowTypes b _ = do
    s <- gets replSettings
    updateSettings (s { showTypes = b })
