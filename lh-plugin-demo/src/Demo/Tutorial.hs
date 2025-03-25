{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Demo.Tutorial where

{-@ ex1 :: {x : Int | x > 2 } @-}
ex1 :: Int
ex1 = 1

{-@ tail' :: xs: {v:[a] | 0 < len v} -> [a] @-}
tail' :: [a] -> [a]
tail' (_ : xs) = xs

a = tail []
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
