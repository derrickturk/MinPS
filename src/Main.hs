{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Check
import Language.MinPS.Eval
import Language.MinPS.Normalize

import Control.Monad.State

bindings :: Context 'Unchecked
bindings =
  [ Declare "Unit" Type
  , Define "Unit" (Enum [MkLabel "unit"])

  , Declare "Nat" Type
  , Define "Nat" (Sigma "l" (Enum [MkLabel "z", MkLabel "s"])
                            (Case (Var "l") [ (MkLabel "z", Var "Unit")
                                            , (MkLabel "s", Rec (Box (Var "Nat")))
                                            ]))

  , Declare "zero" (Var "Nat")
  , Define "zero" (Pair (EnumLabel (MkLabel "z"))
                        (EnumLabel (MkLabel "unit")))

  , Declare "succ" (Pi "_" (Var "Nat") (Var "Nat"))
  , Define "succ" (Lam "n" (Pair (EnumLabel (MkLabel "s"))
                                 (Fold (Var "n"))))

  , Declare "one" (Var "Nat")
  , Define "one" (App (Var "succ") (Var "zero"))

  , Declare "add" (Pi "m" (Var "Nat") (Pi "n" (Var "Nat") (Var "Nat")))
  , Define "add"
      (Lam "m"
        (Lam "n"
          (Split (Var "m") "lm" "m'"
            (Force (Case (Var "lm")
                     [ (MkLabel "z", Box (Var "n"))
                     , (MkLabel "s", Box (App (Var "succ")
                                              (App (App (Var "add")
                                                        (Unfold (Var "m'") "m'"
                                                                (Var "m'")))
                                                   (Var "n"))))
                                    ])))))

  , Declare "zeroPlusZero" (Var "Nat")
  , Define "zeroPlusZero" (App (App (Var "add") (Var "zero")) (Var "zero"))

  , Declare "onePlusZero" (Var "Nat")
  , Define "onePlusZero" (App (App (Var "add") (Var "one")) (Var "zero"))

  , Declare "onePlusOne" (Var "Nat")
  , Define "onePlusOne" (App (App (Var "add") (Var "one")) (Var "one"))
  ]

evalNormal :: Term 'Checked -> Term 'Checked
evalNormal t = evalState (eval t >>= normalize) emptyE

two :: Term 'Unchecked
two = Let bindings (Var "onePlusOne")

nat :: Term 'Unchecked
nat = Let bindings (Var "Nat")

doIt :: Term 'Unchecked -> IO ()
doIt t = do
  case runInfer emptyE (emptyC t) of
    Left e -> print e
    Right (_, two') -> do
      let twoV = runEval emptyE two'
      putStr "eval: "
      print twoV
      let twoN = evalNormal two'
      putStr "normalized: "
      print twoN

main :: IO ()
main = do
  doIt two
  doIt nat
