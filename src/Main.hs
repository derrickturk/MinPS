module Main where

import Language.MinPS.Repl

main :: IO ()
main = banner >> runRepl_ replLoop initialState

banner :: IO ()
banner = do
  putStrLn "    __      __     _       ____"
  putStrLn "   /  \\    /  \\   |_|     |  _ | __"
  putStrLn "  / /\\ \\  / /\\ \\   _  ___ |  __|| _|  by dwt"
  putStrLn " / /  \\ \\/ /  \\ \\ | ||`  || |   |_ |  terminus data science, LLC"
  putStrLn "/_/    \\__/    \\_\\|_||_|_||_|   |__|  (c) 2018"
  putStrLn ""
