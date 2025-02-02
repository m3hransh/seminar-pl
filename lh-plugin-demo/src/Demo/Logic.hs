{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

{-@ LIQUID "--reflection"     @-}
module Demo.Logic where

{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = { v: Bool | not v } @-}

{-@ ==> :: p:Bool -> q:Bool -> {v:Bool | v <=> (p ==> q)} @-}
(==>) :: Bool -> Bool -> Bool
False ==> False = True
False ==> True = True
True ==> True = True
True ==> False = False

{-@ congruence :: (Int -> Int) -> Int -> Int -> TRUE @-}
congruence :: (Int -> Int) -> Int -> Int -> Bool
congruence f x y = (x == y) ==> (f x == f y)

{-@ reflect boolToInt @-}
boolToInt :: Bool -> Int
boolToInt False = 0
boolToInt True = 1

-- {-@ nonNegativeInt :: b:_ -> { boolToInt b >= 0 } @-}
-- nonNegativeInt :: Bool -> ()
-- nonNegativeInt b = ()
--
{-@ type Nat = {v : Int | v > 0 } @-}
{-@ x :: Nat @-}
x :: Int
x = 1
