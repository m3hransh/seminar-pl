module Demo.Proof where

{-@ LIQUID "--reflection"     @-}
import Prelude hiding (reverse, (++))

import Language.Haskell.Liquid.ProofCombinators

{-@ infixr ++ @-}
{-@ reflect ++ @-}

{-@ reflect cons @-}
{-@ cons :: a -> xs: [a] -> {v: [a] | len v == len xs + 1} @-}
cons :: a -> [a] -> [a]
cons x xs = x : xs

{-@ (++) :: xs:[a] -> ys:[a] -> { zs:[a] | len zs == len xs + len ys } @-}
(++) :: [a] -> [a] -> [a]
[] ++ ys = ys
(x : xs) ++ ys = cons x (xs ++ ys)

{-@ prop1:: {v: () | [1] ++ [1] == cons 1 []} @-}
prop1 :: Proof
prop1 = cons 1 ([] ++ [1]) === [1] *** QED

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

-- {-@ rightId' :: xs: [a] -> { v: () | xs ++ [] = xs } @-}
-- rightId' :: [a] -> ()
-- rightId' [] = ()
-- rightId' (x : xs) = rightId' xs
--
-- {-@ assoc' :: xs:[a] -> ys:[a] -> zs:[a] -> { v: () | (xs ++ ys) ++ zs = xs ++ (ys ++ zs) } @-}
-- assoc' :: [a] -> [a] -> [a] -> ()
-- assoc' [] ys zs = ()
-- assoc' (x : xs) ys zs = assoc' xs ys zs

-- https://nikivazou.github.io/lh-course/Lecture_05_ProofsPrograms.html
{-@ reflect fib @-}
{-@ fib :: Nat -> Nat @-}
fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

{-@ fib2_1 :: {fib 2 = 1} @-}

fib2_1 :: ()
fib2_1 =
  fib 2
    === (fib 1 + fib 0 === 1)
    *** QED

{-@ fibThree :: () -> { fib 3 = 2 } @-}
fibThree :: () -> Proof
fibThree _ =
  fib 3
    === (fib 2 + fib 1)
    *** QED

{-@ fibUp :: n:Nat -> { fib n <= fib (n+1) } @-}
fibUp :: Int -> Proof
fibUp 0 =
  fib 0
    =<= fib 1
    *** QED
fibUp 1 =
  fib 1
    =<= fib 1
    + fib 0
      =<= fib 2
      *** QED
fibUp n =
  fib n
    === (fib (n - 1) + fib (n - 2))
    ? fibUp (n - 1)
    =<= (fib n + fib (n - 2))
    ? fibUp (n - 2)
    =<= (fib n + fib (n - 1))
    =<= fib (n + 1)
    *** QED
