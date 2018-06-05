{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.MinPS.Normalize

bindings :: Context 'Checked
bindings =
  [ ("Unit", Type, Enum [MkLabel "unit"])
  , ("Nat", Type, Sigma "l" (Enum [MkLabel "z", MkLabel "s"])
                            (Case (Var 0) [ (MkLabel "z", Var 2)
                                          , (MkLabel "s", Rec (Var 1))
                                          ]))
  , ("Zero", Var 1, Pair (EnumLabel (MkLabel "z"))
                         (EnumLabel (MkLabel "unit")))
  ]

evalNormal :: Term 'Checked -> Term 'Checked
evalNormal t = flip evalEval emptyRecEnv $ do
  t' <- eval t
  normalize t'

main :: IO ()
main = do
  let nat = evalNormal (Let bindings (Var 1))
  print nat
