module Main where

import Language.MinPS.Repl

main :: IO ()
main = banner >> runRepl_ replLoop initialState

banner :: IO ()
banner = do
  putStrLn "It's MinPS!"
  putStrLn ""
