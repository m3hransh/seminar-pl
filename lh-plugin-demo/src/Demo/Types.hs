{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Demo.Types where

{-@ type Zero = {z : Int | z == 0} @-}
{-@ type Even = {z: Int | z mode 2 == 0} @-}

{-@ zero :: Zero @-}
zero :: Int
zero = 0

{-@ evenList :: [Even] @-}
evenList :: [Int]
evenList = [2, 4]

{-@ impossible :: {v: String | false} -> a @-}
impossible :: String -> a
impossible msg = error msg

{-@ type NonZero = {v: Int | v /= 0} @-}

{-@ divide' :: Int -> NonZero -> Int @-}
divide' :: Int -> Int -> Int
divide' x 0 = impossible "divide by zero"
divide' x y = x `div` y

avg :: [Int] -> Int
avg [] = 0
avg xs = divide' total n
 where
  total = sum xs
  n = length xs
