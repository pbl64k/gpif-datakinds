{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}

module Control.IxFunctor.Iso
    ( Isomorphic(from, to)
    , isoToLeft
    , isoToRight
    ) where

class Isomorphic a b where
    from :: a -> b

    to :: b -> a

instance Isomorphic a a where
    from = id

    to = id

isoToLeft :: (Isomorphic c a, Isomorphic d b) => (a -> b) -> c -> d
isoToLeft f = to . f . from

isoToRight :: (Isomorphic a c, Isomorphic b d) => (a -> b) -> c -> d
isoToRight f = from . f . to

