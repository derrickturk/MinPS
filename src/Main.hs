{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value

bindings :: Context 'Checked
bindings =
  [ ("Unit", Type, Enum [MkLabel "unit"])
  , ("Nat", Type, Sigma "l" (Enum [MkLabel "z", MkLabel "s"])
                            (Case (Var 0) [ (MkLabel "z", Var 2)
                                          , (MkLabel "s", Rec (Var 1))
                                          ]))
  , ("Zero", Var 1, Pair (EnumLabel (MkLabel "z")) (Var 2))
  ]

main :: IO ()
main = do
  let nat = evalEval (eval $ Let bindings (Var 1)) emptyRecEnv
  case nat of
    VSigma _ x ty t -> putStrLn $
      "Nat is (Sigma " ++ show x ++ " (" ++ show ty ++ ") (" ++ show t ++ ")"
    VType -> putStrLn "Nat went lambda"
    VLam _ _ _ -> putStrLn "Nat went lambda"
    VPi _ _ _ _ -> putStrLn "Nat went pi"
    VNeutral _ -> putStrLn "Nat went Neutral"
    VBox _ t -> putStrLn $ "Nat went Box " ++ show t
    VRec _ t -> putStrLn $ "Nat went Rec " ++ show t
    _ -> putStrLn "Nat went wrong"
