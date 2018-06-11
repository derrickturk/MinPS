{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts, LambdaCase, GeneralizedNewtypeDeriving #-}

module Language.MinPS.Environment (
    Scope
  , Closure(..)
  , EnvEntry(..)
  , Constraints(..)
  , Env
  , setEnv
  , lookupSE
  , lookupE
  , declareE
  , defineE
  , repointE
  , emptyS
  , emptyC
  , emptyE
  , locally
) where

import Language.MinPS.Syntax
import Language.MinPS.Closure
import Language.MinPS.Value

import Control.Monad.State
import qualified Data.Sequence as S

-- ok, sooooooooo
-- we've got to be able to define values (and thus declare new slots)
--   for unknown-type terms
--   (think: evaluating function application)
-- as well as declare types without values yet
-- oh yeah, and for extra fun, undefined terms need to be re-pointable
--   (i.e. "i'm not defined, but if I were I'd be the same as the guy
--      over there") to support certain wacky corner cases of equality
--      checking
data EnvEntry = EnvEntry { envName :: Ident
                           -- declared as a known type, or not
                         , envType :: Maybe (Closure (Term 'Checked))
                           -- defined as a term, or pointed to an
                           --   environment slot (its own, by default, but the
                           --   equality checker will twiddle this)
                         , envValue :: Either Int (Closure (Term 'Checked))
                         } deriving Show

data Constraints =
    Inconsistent
  | Constraints [(Neutral, Label)]
  deriving Show

data Env = Env { getEnv :: S.Seq EnvEntry
               , getConstraints :: Constraints
               }
  deriving Show

setEnv :: S.Seq EnvEntry -> Env -> Env
setEnv e (Env _ consts) = Env e consts

lookupSE :: Ident -> Scope -> Env -> Maybe (EnvEntry, Int)
lookupSE x s e = lookup x s >>= \i -> lookupE i e >>= \ee -> pure (ee, i)

lookupE :: Int -> Env -> Maybe EnvEntry
lookupE i e = S.lookup i $ getEnv e

declareE :: MonadState Env m
         => Ident
         -> Maybe (Closure (Term 'Checked))
         -> m Int
declareE x ty = do
  env <- gets getEnv
  let next = S.length env
  modify $ setEnv (env S.:|> EnvEntry x ty (Left next))
  pure next

defineE :: MonadState Env m => Int -> Closure (Term 'Checked) -> m ()
defineE i t = do
  env <- gets getEnv
  modify $ setEnv (S.adjust' (install t) i env)
  where
    install val (EnvEntry x ty _) = EnvEntry x ty (Right val)

repointE :: MonadState Env m => Int -> Int -> m ()
repointE i j = do
  env <- gets getEnv
  modify $ (setEnv (S.adjust' (repoint j) i env))
  where
    repoint idx (EnvEntry x ty _) = EnvEntry x ty (Left idx)

emptyS :: Scope
emptyS = []

emptyC :: a -> Closure a
emptyC = (:@ emptyS)

emptyE :: Env
emptyE = Env S.empty (Constraints [])

locally :: MonadState s m => m a -> m a
locally m = get >>= \s -> m >>= \x -> put s >> pure x
