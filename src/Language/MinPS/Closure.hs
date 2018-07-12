{-# LANGUAGE GADTs, KindSignatures, StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Language.MinPS.Closure (
    Scope
  , Ident(..)
  , Closure(..)
) where

import Data.String (IsString)
import Data.List (intercalate)
import qualified Data.Text as T

newtype Ident = MkIdent { getIdent :: T.Text }
  deriving (Show, Eq, IsString, Ord)

type Scope = [(Ident, Int)]

data Closure :: * -> * where
  (:@) :: a -> Scope -> Closure a
infix 4 :@

instance Show a => Show (Closure a) where
  show (x :@ []) = show x
  show (x :@ c) = show x ++ "[with " ++ intercalate ", " binds ++ "]" where
    binds = fmap (\(var, i) -> T.unpack (getIdent var) ++ "@" ++ show i) c

deriving instance Eq a => Eq (Closure a)
