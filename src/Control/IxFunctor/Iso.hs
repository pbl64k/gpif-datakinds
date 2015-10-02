{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}

{-|
Module      : Control.IxFunctor.Iso
Description : Isomorphisms between types
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

-}

module Control.IxFunctor.Iso
    ( Isomorphic(from, to)
    , isoToLeft
    , isoToRight
    ) where

-- |Isomorphism between two types.
class Isomorphic a b where
    from :: a -> b

    to :: b -> a

instance Isomorphic a a where
    from = id

    to = id

-- |Given a function operating on the types on the right side of the two isomorphisms,
-- produces a function operating on the types on the left side of the same isomorphisms.
isoToLeft :: (Isomorphic c a, Isomorphic d b) => (a -> b) -> c -> d
isoToLeft f = to . f . from

-- |Given a function operating on the types on the left side of the two isomorphisms,
-- produces a function operating on the types on the right side of the same isomorphisms.
isoToRight :: (Isomorphic a c, Isomorphic b d) => (a -> b) -> c -> d
isoToRight f = from . f . to

