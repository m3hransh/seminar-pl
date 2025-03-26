{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Demo.Sorting where

import Data.Set (Set)
import qualified Data.Set as Set
import Language.Haskell.Liquid.Bag as B
import Language.Haskell.Liquid.ProofCombinators
import Prelude hiding (id, sum)

data List a = Nil | Cons a (List a) deriving (Eq, Show)

{-@ measure bag @-}
{-@ bag :: Ord a => List a -> Bag a @-}
bag :: (Ord a) => List a -> B.Bag a
bag Nil = B.empty
bag (Cons x xs) = B.put x (bag xs)

{-@ reflect singelton @-}
{-@ singelton ::  a -> Bag a @-}
singelton :: (Ord a) => a -> B.Bag a
singelton x = B.put x (B.empty)

-- {-@ equalBag :: { bag(Cons 1 (Cons 3 Nil)) ==  (bag( Cons 2 Nil)) } @-}
-- equalBag = ()

{-@ reflect isSorted @-}
isSorted :: (Ord a) => List a -> Bool
isSorted Nil = True
isSorted (Cons x xs) =
  isSorted xs && case xs of
    Nil -> True
    Cons x1 xs1 -> x <= x1

{-@ sortedList :: { isSorted (Cons 1 (Cons 2  Nil))} @-}
sortedList :: ()
sortedList =
  isSorted (Cons 1 (Cons 2 Nil))
    === (isSorted (Cons 2 Nil) && 1 <= 2)
    === True
    *** QED

{-@ reflect insert @-}
{-@ insert :: x:_ -> {xs:_ | isSorted xs} -> {ys:_ | isSorted ys && Map_union (singelton x) (bag xs) == bag ys  } @-}
insert :: (Ord a) => a -> List a -> List a
insert x Nil = Cons x Nil
insert x (Cons y ys)
  | x <= y = Cons x (Cons y ys)
  | otherwise = Cons y (insert x ys) `withProof` lem_ins y x ys

{-@ lem_ins :: y:_ -> {x:_ | y < x} -> {ys: _ | isSorted (Cons y ys)} -> {isSorted (Cons y (insert x ys))} @-}
lem_ins :: (Ord a) => a -> a -> List a -> Bool
lem_ins y x Nil = True
lem_ins y x (Cons y1 ys) = if y1 < x then lem_ins y1 x ys else True

{-@ insertSort :: xs:_ -> {ys:_ | isSorted ys && bag xs == bag ys} @-}
insertSort :: (Ord a) => List a -> List a
insertSort Nil = Nil
insertSort (Cons x xs) = insert x (insertSort xs)

-- {-@ foo :: xs:[Int] -> ys:[Int] ->  {bag xs == bag ys} @-}
-- foo :: [Int] -> [Int] -> () -> ()
-- foo _ _ _ = ()
