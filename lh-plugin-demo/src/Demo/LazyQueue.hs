module Demo.LazyQueue where

import Demo.Types (impossible)

{-@ LIQUID "--reflection"     @-}
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

{-@ cons :: a -> xs:SList a -> SListN a {size xs + 1} @-}
cons x (SL n xs) = SL (n + 1) (x : xs)

{-@ tl :: {xs:SList a | size xs > 0} -> SListN a {size xs - 1} @-}
tl (SL n (_ : xs)) = SL (n - 1) xs
tl _ = impossible "Empty SList"

{-@ hd :: {xs:SList a | size xs > 0} -> a @-}
hd (SL _ (x : _)) = x
hd _ = impossible "Empty SList"

{-@ type SListLE a N = {v:SList a | size v <= N} @-}

{-@ data Queue a = Q {
      front :: SList a
    , back  :: SListLE a (size front)
    }
@-}
data Queue a = Q
  { front :: SList a
  , back :: SList a
  }

{-@ measure queueSize @-}
{-@ queueSize :: Queue a -> Int @-}
queueSize :: Queue a -> Int
queueSize (Q f b) = size f + size b

{-@ type QueueN a N = {v:Queue a | queueSize v = N} @-}

emp = Q nil nil

-- remove (Q f b) = (hd f, makeq (tl f) b)

{-@ example3Q :: QueueN _ 3 @-}
example3Q = Q (1 `cons` (2 `cons` nil)) (3 `cons` nil)

--
{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil
