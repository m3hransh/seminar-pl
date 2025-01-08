{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

module Demo.Tutorial where

{-@ tail' :: xs: {v:[a] | 0 < len v} -> {v:[a] | len v == len xs - 1} @-}
tail' :: [a] -> [a]
tail' (_ : xs) = xs

x :: [Int]
x = tail' (tail' [1, 2])

test :: [Int] -> Int -> Maybe Int
test xs i =
  case xs of
    [] -> Nothing
    (x : _) ->
      if i >= 0 && i < length xs
        then Just x
        else Nothing

l = test [] 2
