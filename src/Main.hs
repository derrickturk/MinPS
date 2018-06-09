{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.MinPS.Syntax
import Language.MinPS.Eval
import Language.MinPS.Value
import Language.MinPS.Normalize

bindings :: Context 'Checked
bindings =
  [ Declare "Unit" Type
  , Define "Unit" (Enum [MkLabel "unit"])

  , Declare "Nat" Type
  , Define "Nat" (Sigma "l" (Enum [MkLabel "z", MkLabel "s"])
                            (Case (Var 0) [ (MkLabel "z", Var 2)
                                          , (MkLabel "s", Rec (Var 1))
                                          ]))

  , Declare "zero" (Var 1)
  , Define "zero" (Pair (EnumLabel (MkLabel "z"))
                        (EnumLabel (MkLabel "unit")))

  , Declare "succ" (Pi "_" (Var 2) (Var 2))
  , Define "succ" (Lam "n" (Pair (EnumLabel (MkLabel "s"))
                                 (Fold (Var 0))))

  , Declare "one" (Var 3)
  , Define "one" (App (Var 1) (Var 2))

  , Declare "add" (Pi "m" (Var 4) (Pi "n" (Var 5) (Var 5)))
  , Define "add"
      (Lam "m"
        (Lam "n"
          (Split (Var 1) "lm" "m'"
            (Force (Case (Var 1)
                     [ (MkLabel "z", Box (Var 2))
                     , (MkLabel "s", Box (App (Var 6)
                                              (App (App (Var 4)
                                                        (Unfold (Var 0) "_"
                                                                (Var 0)))
                                                   (Var 2))))
                                    ])))))
  , Declare "onePlusOne" (Var 5)
  , Define "onePlusOne" (App (App (Var 1) (Var 2)) (Var 2))
  ]

evalNormal :: Term 'Checked -> Term 'Checked
evalNormal t = flip evalEval emptyRecEnv $ do
  t' <- eval t
  normalize t'

main :: IO ()
main = do
  let one = evalNormal (Let bindings (Var 0))
  print one
