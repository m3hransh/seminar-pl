module Demo.LazyQueue where

import Demo.Types (impossible)

{-@ measure realSize @-}
realSize :: [a] -> Int
realSize [] = 0
realSize (_ : xs) = 1 + realSize xs

{-@ data SList a = SL {size :: Int, elems :: {v: [a] | realSize v == size}} @-}
data SList a = SL {size :: Int, elems :: [a]}

okList = SL 2 [1, 2]

{-@ type SListN a N = { v: SList a | size v = N} @-}

{-@ nil :: SListN a 0 @-}
nil = SL 0 []

{-@ cons :: x:a -> xs:SList a -> SListN a {size xs + 1} @-}
cons x (SL n xs) = SL (n + 1) (x : xs)

{-@ tl :: {xs:SList a | size xs > 0} -> SListN a {size xs - 1} @-}
tl (SL n (_ : xs)) = SL (n - 1) xs
tl _ = impossible "Empty SList"

{-@ head :: {xs:SList a | size xs > 0} -> a @-}
head (SL _ (x : _)) = x
head _ = impossible "Empty SList"
