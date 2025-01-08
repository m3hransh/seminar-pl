module Demo.Measure where

import Prelude hiding (head, null)

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

{-@ type ListN a N = {v: [a] | size v = N} @-}
{-@ type ListX a X = ListN a {size X}        @-}
{-@ measure size @-}
{-@ size :: xs: [a] -> {v: Nat | notEmpty xs <=> v > 0}  @-}
size :: [a] -> Int
size [] = 0
size (_ : rs) = 1 + size rs

{-@ measure len @-}
{-@ len :: xs: [a] -> {v: Nat | notEmpty xs => v > 0}  @-}
len :: [a] -> Int
len [] = 0
len (_ : rs) = 1 + len rs

{-@ example:: ListN Int 3 @-}
example :: [Int]
example = [1, 2, 3]

{-@ reverse       :: xs:[a] -> ListX a xs @-}
reverse xs = go [] xs
 where
  {-@ go :: acc:[a] -> xs:List a -> ListN a { size acc + size xs} @-}
  go acc [] = acc
  go acc (x : xs) = go (x : acc) xs

data Slist' a = Slist' {listSize :: Int, elems :: [a]}

{-@ data Slist' a = Slist' { listSize :: Nat, elems :: {v:[a] | len v == listSize} } @-}
{-@ okList :: Slist' Int  @-}
okList :: Slist' Int
okList = Slist' 2 [1, 2]

{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty [] = False
notEmpty (_ : _) = True

{-@ type NEList a = { v: [a] | notEmpty v } @-}
{-@ average :: NEList Int -> Int @-}
average :: [Int] -> Int
average xs = sum xs `div` size xs

average' :: [Int] -> Maybe Int
average' xs
  | ok = Just $ div (sum xs) elems
  | otherwise = Nothing
 where
  elems = size xs
  ok = elems > 0 -- What expression goes here?

-- This is rejected because the line 1 + size2 xs
-- LH can't reason that size2 xs could be Nat so that
-- {-@ size2    :: xs:[a] -> {v:Int | notEmpty xs => v > 0} @-}
-- size2 :: [a] -> Int
-- size2 [] = 0
-- size2 (_ : xs) = 1 + size2 xs
-- T
-- {-@ size1    :: xs:NEList a -> {v: Int | v >= 0 }@-}
-- size1 :: [a] -> Int
-- size1 [] = 0
-- size1 (_ : xs) = 1 + size1 xs

{-@ head :: NEList a -> a @-}
head :: [a] -> a
head (x : _) = x

safeHead :: [a] -> Maybe a
safeHead xs
  | null xs = Nothing
  | otherwise = Just $ head xs

{-@ measure null @-}
{-@ null      :: xs :[a] -> {v: Bool | null xs == false => size xs > 0} @-}
null [] = True
null (_ : _) = False

{-@ groupEq    :: (Eq a) => [a] -> [NEList a] @-}
groupEq :: (Eq a) => [a] -> [[a]]
groupEq [] = []
groupEq (x : xs) = (x : ys) : groupEq zs
 where
  (ys, zs) = span (x ==) xs

eliminateStutter :: (Eq a) => [a] -> [a]
eliminateStutter xs = map head $ groupEq xs
