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

zero : Nat;
zero = ('z, 'unit);

succ : Nat -> Nat;
succ = \n -> ('s, fold n);

one : Nat;
one = succ zero;

add : (m: Nat) -> (n: Nat) -> Nat;
add = \m n -> split m with (lm, m') -> !case lm of {
    z -> [n]
  | s -> [succ (add (unfold m') n)]
};

zeroPlusZero : Nat;
zeroPlusZero = add zero zero;

onePlusZero : Nat;
onePlusZero = add one zero;

onePlusOne : Nat;
onePlusOne = add one one;

Void : Type;
Void = {};

Fin : (n: Nat) -> Type;
Fin = \n -> split n with (ln, n') -> !case ln of {
    z -> [Void]
  | s -> [(l: {z s}) * case l of {
        z -> Unit
      | s -> Fin (unfold n')
    }]
};

fz : (n: Nat) -> Fin (succ n);
fz = \n -> ('z, 'unit);

fs : (n: Nat) -> (i: Fin n) -> Fin (succ n);
fs = \n i -> ('s, i);
|]

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
