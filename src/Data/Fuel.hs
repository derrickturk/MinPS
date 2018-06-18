module Data.Fuel (
    Fuel(..)
  , fuel
  , infiniteFuel
) where

data Fuel =
    Empty
  | More Fuel
  deriving Show

fuel :: Int -> Fuel
fuel x
  | x <= 0 = Empty
  | otherwise = More $ fuel (x - 1)

infiniteFuel :: Fuel
infiniteFuel = More infiniteFuel
