module Demo.Proof where

{-@ LIQUID "--reflection"     @-}
import Prelude hiding (reverse, (++))

import Language.Haskell.Liquid.ProofCombinators

{-@ infixr ++ @-}
{-@ reflect ++ @-}

{-@ (++) :: xs:[a] -> ys:[a] -> { zs:[a] | len zs == len xs + len ys } @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x : xs) ++ ys = x : (xs ++ ys)

{-@ rightId :: xs: [a] -> { v: () | xs ++ [] = xs } @-}
rightId :: [a] -> ()
rightId [] = [] ++ [] === [] *** QED
rightId (x : xs) = (x : xs) ++ [] === x : (xs ++ []) ? rightId xs === x : xs *** QED

{-@ assoc :: xs:[a] -> ys:[a] -> zs:[a] -> { v: () | (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
assoc :: [a] -> [a] -> [a] -> ()
assoc [] ys zs =
  ([] ++ ys)
    ++ zs
    === ys
    ++ zs
    === []
    ++ (ys ++ zs)
    *** QED
assoc (x : xs) ys zs =
  ((x : xs) ++ ys)
    ++ zs
    === ( x
            : (xs ++ ys)
        )
    ++ zs
    === x
    : ((xs ++ ys) ++ zs)
      ? assoc xs ys zs
      === (x : xs)
      ++ (ys ++ zs)
      *** QED

-- {-@ LIQUID "--ple" @-}

-- {-@ rightId' :: xs: [a] -> { v: () | xs ++ [] = xs } @-}
-- rightId' :: [a] -> ()
-- rightId' [] = ()
-- rightId' (x : xs) = rightId' xs
--
-- {-@ assoc' :: xs:[a] -> ys:[a] -> zs:[a] -> { v: () | (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
-- assoc' :: [a] -> [a] -> [a] -> ()
-- assoc' [] ys zs = ()
-- assoc' (x : xs) ys zs = assoc' xs ys zs

{-@ reflect fib @-}
{-@ fib :: Nat -> Nat @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

{-@ fib2_1 :: {fib 2 = 1} @-}

{-@ LIQUID "--ple" @-}
fib2_1 :: ()
fib2_1 = ()
