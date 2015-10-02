{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

{-|
Module      : Control.IxFunctor.Nat
Description : Natural numbers
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

Natural numbers encoded through indexed functors.
-}

module Control.IxFunctor.Nat
        ( NatFunctor
        , Nat
        , fromIntegerToNat
        , toIntegerFromNat
        , cataInteger
        , anaInteger
        , hyloInteger
        , paraInteger
        , apoInteger
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme

-- |Base functor for natural numbers -- X. 1 + X
type NatFunctor = ((IxUnit :+: IxProj (Right '())) :: (Either Void () -> *) -> () -> *)

-- |Fix X. 1 + X
type Nat = IxFix NatFunctor

-- |Conversion from `Integer` to `Nat` expressed as anamorphism on nats.
fromIntegerToNat :: Integer -> Nat IxTVoid ix
fromIntegerToNat = (coalgebra `ixana`) . from
    where
        coalgebra :: IxTConst Integer :-> NatFunctor (IxTVoid `IxTEither` IxTConst Integer)
        coalgebra (IxTConst 0) = IxLeft $ from ()
        coalgebra (IxTConst n) = IxRight $ from $ pred n

-- |Conversion from `Nat` to `Integer` expressed as catamorphism on nats.
toIntegerFromNat :: Nat IxTVoid ix -> Integer
toIntegerFromNat = to . (algebra `ixcata`)
    where
        algebra :: NatFunctor (IxTVoid `IxTEither` IxTConst Integer) :-> IxTConst Integer
        algebra (IxLeft _) = IxTConst 0
        algebra (IxRight x) = IxTConst $ succ $ to x

-- |For some values of "isomorphic". Don't try this with negative numbers.
instance Isomorphic Integer (Nat IxTVoid ix) where
    from = fromIntegerToNat

    to = toIntegerFromNat

-- |Fold for non-negative integers.
cataInteger :: forall a. (Maybe a -> a) -> Integer -> a
cataInteger algebra = isoToLeft (alg `ixcata`)
    where
        alg :: NatFunctor (IxTVoid `IxTEither` IxTConst a) :-> IxTConst a
        alg = isoToRight algebra

-- |Unfold for non-negative integers.
anaInteger :: forall a. (a -> Maybe a) -> a -> Integer
anaInteger coalgebra = isoToLeft (coalg `ixana`)
    where
        coalg :: IxTConst a :-> NatFunctor (IxTVoid `IxTEither` IxTConst a)
        coalg = isoToRight coalgebra

hyloInteger :: forall a b. (Maybe b -> b) -> (a -> Maybe a) -> a -> b
hyloInteger algebra coalgebra = isoToLeft $ ixhylo alg coalg
    where
        alg :: NatFunctor (IxTVoid `IxTEither` IxTConst b) :-> IxTConst b
        alg = isoToRight algebra
        coalg :: IxTConst a :-> NatFunctor (IxTVoid `IxTEither` IxTConst a)
        coalg = isoToRight coalgebra

paraInteger :: forall a. (Maybe (a, Integer) -> a) -> Integer -> a
paraInteger algebra = isoToLeft (alg `ixpara`)
    where
        alg :: NatFunctor (IxTVoid `IxTEither` (IxTConst a `IxTPair` Nat IxTVoid)) :-> IxTConst a
        alg = isoToRight algebra

apoInteger :: forall a. (a -> Maybe (Either a Integer)) -> a -> Integer
apoInteger coalgebra = isoToLeft (coalg `ixapo`)
    where
        coalg :: IxTConst a :-> NatFunctor (IxTVoid `IxTEither` (IxTConst a `IxTChoice` Nat IxTVoid))
        coalg = isoToRight coalgebra

