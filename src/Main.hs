{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings, QuasiQuotes #-}

module Main where

import Language.MinPS.Parse
import Language.MinPS.Syntax
import Language.MinPS.Environment
import Language.MinPS.Check
import Language.MinPS.Eval
import Language.MinPS.Normalize

import Control.Monad.State

import qualified Data.Text as T
import Text.RawString.QQ

bindings :: T.Text
bindings = [r|Unit : Type;
Unit = { unit };
Nat : Type;
Nat = (l : {z s}) * case l of { z -> Unit | s -> Rec [Nat] };
Zero : Nat;
Zero = ('z, 'unit);
|]

{-
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

  , Declare "Void" Type
  , Define "Void" (Enum [])

  , Declare "Fin" (Pi "n" (Var "Nat") Type)
  , Define "Fin" (Lam "n"
                   (Split (Var "n") "ln" "n'"
                          (Force (Case (Var "ln")
                                       [ ("z", Box (Var "Void"))
                                       , ("s", Box (Sigma "l"
                                                     (Enum ["z", "s"])
                                                     (Case (Var "l")
                                                           [ ("z", Var "Unit")
                                                           , ("s", App (Var "Fin") (Unfold (Var "n'") "n'" (Var "n'")))
                                                           ])))
                                       ]))))

  , Declare "fz" (Pi "n" (Var "Nat")
                         (App (Var "Fin") (App (Var "succ") (Var "n"))))
  , Define "fz" (Lam "n" (Pair (EnumLabel "z") (EnumLabel "unit")))

  , Declare "fs" (Pi "n" (Var "Nat")
                         (Pi "i" (App (Var "Fin") (Var "n"))
                                 (App (Var "Fin") (App (Var "succ") (Var "n")))))
  , Define "fs" (Lam "n" (Lam "i" (Pair (EnumLabel "s") (Var "i"))))
  ]
-}

evalNormal :: Term 'Checked -> Term 'Checked
evalNormal t = evalState (eval t >>= normalize) emptyE

terms :: Context 'Unchecked -> [Term 'Unchecked]
terms ctxt = [ Let ctxt (Var "onePlusOne")
             , Let ctxt (Var "Nat")
             , Let ctxt (App (Var "fz") (Var "onePlusOne"))
             , Let ctxt (App (App (Var "fs") (Var "onePlusOne"))
                             (App (Var "fz") (Var "one")))
             ]

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
  let ctxt = parse (only context) "" bindings
  case ctxt of
    Right ctxt' -> mapM_ doIt (terms ctxt')
    Left e -> putStrLn $ parseErrorPretty e
