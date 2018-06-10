{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Environment (
    Scope
  , Closure
  , EnvEntry(..)
  , Env
  , lookupSE
  , lookupE
) where

import Language.MinPS.Syntax

import Control.Monad.State
import Data.List (intercalate)
import qualified Data.Sequence as S
import qualified Data.Text as T

type Scope = [(Ident, Int)]

data Closure :: * -> * where
  Closure :: Scope -> a -> Closure a

data EnvEntry = EnvEntry { envValue :: Maybe (Closure (Term 'Checked))
                         , envType :: Closure (Term 'Checked)
                         } deriving Show

newtype Env = Env { getEnv :: S.Seq EnvEntry }
  deriving Show

lookupSE :: Ident -> Scope -> Env -> Maybe EnvEntry
lookupSE x s e = lookup x s >>= \i -> lookupE i e

lookupE :: Int -> Env -> Maybe EnvEntry
lookupE i e = S.lookup i $ getEnv e

declareE :: MonadState Env m => Closure (Term 'Checked) -> m Int
declareE ty = do
  env <- gets getEnv
  let next = S.length env
  put $ Env $ env S.:|> EnvEntry Nothing ty
  pure next

defineE :: MonadState Env m => Int -> Closure (Term 'Checked) -> m ()
defineE i t = do
  env <- gets getEnv
  put $ Env $ S.adjust' (install t) i env
  where
    install t (EnvEntry _ ty) = EnvEntry (Just t) ty

instance Show a => Show (Closure a) where
  show (Closure [] x) = show x
  show (Closure c x) = show x ++ "[with " ++ intercalate ", " binds ++ "]" where
    binds = fmap (\(x, i) -> T.unpack (getIdent x) ++ "@" ++ show i) c
