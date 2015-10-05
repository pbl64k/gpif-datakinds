{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Control.IxFunctor.List
Description : Cons-cell lists
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

Cons-cell lists encoded through indexed functors.
-}

module Control.IxFunctor.List
        ( ListFunctor
        , List
        , fromList
        , toList
        , mapList
        , cataList
        , anaList
        , hyloList
        , paraList
        , apoList
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme

-- |Base functor for lists, X. 1 + A x X
type ListFunctor = ((IxUnit :+: (IxProj (Left '()) :*: IxProj (Right '()))) :: (Either () () -> *) -> () -> *)

-- |Fix X. 1 + A x X
type List = IxFix ListFunctor

fromList :: forall a b ix. Isomorphic a (b '()) => [a] -> List b ix
fromList = (coalgebra `ixana`) . from
    where
        coalgebra :: IxTConst [a] :-> ListFunctor (b `IxTEither` IxTConst [a])
        coalgebra (IxTConst []) = IxLeft $ from ()
        coalgebra (IxTConst (x : xs)) = IxRight $ from (x, xs)

toList :: forall a b ix. Isomorphic a (b '()) => List b ix -> [a]
toList = to . (algebra `ixcata`)
    where
        algebra :: ListFunctor (b `IxTEither` IxTConst [a]) :-> IxTConst [a]
        algebra (IxLeft _) = IxTConst []
        algebra (IxRight xs) = IxTConst (to x : xs')
            where
                z :: (b '(), [a])
                z@(x, xs') = to xs

instance Isomorphic a (b '()) => Isomorphic [a] (List b ix) where
    from = fromList

    to = toList

-- |`fmap` for lists falls out of it almost for free.
mapList :: (a -> b) -> [a] -> [b]
mapList f = to . (liftIxTConst f `ixmap`) . fromList

-- |The well-known `foldr` in a slightly unusual (but aesthetically pleasing) form.
cataList :: forall a b. (Maybe (b, a) -> a) -> [b] -> a
cataList algebra = isoToLeft (alg `ixcata`)
    where
        alg :: ListFunctor (IxTConst b `IxTEither` IxTConst a) :-> IxTConst a
        alg = isoToRight algebra

-- |List unfold.
anaList :: forall a b. (a -> Maybe (b, a)) -> a -> [b]
anaList coalgebra = isoToLeft (coalg `ixana`)
    where
        coalg :: IxTConst a :-> ListFunctor (IxTConst b `IxTEither` IxTConst a)
        coalg = isoToRight coalgebra

hyloList :: forall a b c. (Maybe (b, c) -> c) -> (a -> Maybe (b, a)) -> a -> c
hyloList algebra coalgebra = isoToLeft $ ixhylo alg coalg
    where
        alg :: ListFunctor (IxTConst b `IxTEither` IxTConst c) :-> IxTConst c
        alg = isoToRight algebra
        coalg :: IxTConst a :-> ListFunctor (IxTConst b `IxTEither` IxTConst a)
        coalg = isoToRight coalgebra

paraList :: forall a b. (Maybe (b, (a, [b])) -> a) -> [b] -> a
paraList algebra = isoToLeft (alg `ixpara`)
    where
        alg :: ListFunctor (IxTConst b `IxTEither` (IxTConst a `IxTPair` List (IxTConst b))) :-> IxTConst a
        alg = isoToRight algebra

apoList :: forall a b. (a -> Maybe (b, (Either a [b]))) -> a -> [b]
apoList coalgebra = isoToLeft (coalg `ixapo`)
    where
        coalg :: IxTConst a :-> ListFunctor (IxTConst b `IxTEither` (IxTConst a `IxTChoice` List (IxTConst b)))
        coalg = isoToRight coalgebra

