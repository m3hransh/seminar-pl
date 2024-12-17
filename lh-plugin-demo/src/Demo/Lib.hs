{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Demo.Lib where

-- {-@ reflect smartInsert @-}
-- smartInsert :: String -> Int -> [(String, Int)] -> [(String, Int)]
-- smartInsert k v l
--   | lookup k l == Just v = l
--   | otherwise = (k, v) : l
