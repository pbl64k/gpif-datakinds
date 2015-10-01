{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Control.IxFunctor.Rose
        ( RoseFunctor
        , Rose
        , fromRose
        , toRose
        , mapRose
        , cataRose
        , anaRose
        , hyloRose
        , paraRose
        , apoRose
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme
import Control.IxFunctor.List

data RoseTree a = RoseTree a [RoseTree a] deriving Show

type RoseFunctor = ((IxProj (Left '()) :*: (List :.: IxProj (Right '()))) :: (Either () () -> *) -> () -> *)

type Rose = IxFix RoseFunctor

fromRose :: forall a b ix. Isomorphic a (b '()) => RoseTree a -> Rose b ix
fromRose = (coalgebra `ixana`) . from
    where
        coalgebra :: forall ix. IxTConst (RoseTree a) ix -> RoseFunctor (b `IxTEither` IxTConst (RoseTree a)) ix
        coalgebra (IxTConst (RoseTree x xs)) = from x `IxProd` from xs

toRose :: forall a b ix. Isomorphic a (b '()) => Rose b ix -> RoseTree a
toRose = to . (algebra `ixcata`)
    where
        algebra :: forall ix. RoseFunctor (b `IxTEither` IxTConst (RoseTree a)) ix -> IxTConst (RoseTree a) ix
        algebra (x `IxProd` xs) = IxTConst $ RoseTree (to x) (to xs)

instance Isomorphic a (b '()) => Isomorphic (RoseTree a) (Rose b ix) where
    from = fromRose

    to = toRose

mapRose :: (a -> b) -> RoseTree a -> RoseTree b
mapRose f = toRose . (liftIxTConst f `ixmap`) . fromRose

cataRose :: forall a b. ((a, [b]) -> b) -> RoseTree a -> b
cataRose algebra = isoToLeft (alg `ixcata`)
    where
        alg :: RoseFunctor (IxTConst a `IxTEither` IxTConst b) :-> IxTConst b
        alg = isoToRight algebra

anaRose :: forall a b. (b -> (a, [b])) -> b -> RoseTree a
anaRose coalgebra = isoToLeft (coalg `ixana`)
    where
        coalg :: IxTConst b :-> RoseFunctor (IxTConst a `IxTEither` IxTConst b)
        coalg = isoToRight coalgebra

hyloRose :: forall a b c. ((b, [c]) -> c) -> (a -> (b, [a])) -> a -> c
hyloRose algebra coalgebra = isoToLeft (ixhylo alg coalg)
    where
        alg :: RoseFunctor (IxTConst b `IxTEither` IxTConst c) :-> IxTConst c
        alg = isoToRight algebra
        coalg :: IxTConst a :-> RoseFunctor (IxTConst b `IxTEither` IxTConst a)
        coalg = isoToRight coalgebra

paraRose :: forall a b. ((a, [(b, RoseTree a)]) -> b) -> RoseTree a -> b
paraRose algebra = isoToLeft (alg `ixpara`)
    where
        alg :: RoseFunctor (IxTConst a `IxTEither` (IxTConst b `IxTPair` Rose (IxTConst a))) :-> IxTConst b
        alg = isoToRight algebra

apoRose :: forall a b. (b -> (a, [Either b (RoseTree a)])) -> b -> RoseTree a
apoRose coalgebra = isoToLeft (coalg `ixapo`)
    where
        coalg :: IxTConst b :-> RoseFunctor (IxTConst a `IxTEither` (IxTConst b `IxTChoice` Rose (IxTConst a)))
        coalg = isoToRight coalgebra

