{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module Control.IxFunctor.Nat
        ( NatFunctor
        , Nat
        , fromIntegerToNat
        , toIntegerFromNat
        , cataInteger
        , anaInteger
        , hyloInteger
        , paraInteger
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme

type NatFunctor = ((IxUnit :+: IxProj (Right '())) :: (Either Void () -> *) -> () -> *)

type Nat = IxFix NatFunctor

fromIntegerToNat :: Integer -> Nat IxTVoid ix
fromIntegerToNat = (coalgebra `ixana`) . from
    where
        coalgebra :: IxTConst Integer :-> NatFunctor (IxTVoid `IxTEither` IxTConst Integer)
        coalgebra (IxTConst 0) = IxLeft $ from ()
        coalgebra (IxTConst n) = IxRight $ from $ pred n

toIntegerFromNat :: Nat IxTVoid ix -> Integer
toIntegerFromNat = to . (algebra `ixcata`)
    where
        algebra :: NatFunctor (IxTVoid `IxTEither` IxTConst Integer) :-> IxTConst Integer
        algebra (IxLeft _) = IxTConst 0
        algebra (IxRight x) = IxTConst $ succ $ to x

instance Isomorphic Integer (Nat IxTVoid ix) where
    from = fromIntegerToNat

    to = toIntegerFromNat

cataInteger :: forall a. (Maybe a -> a) -> Integer -> a
cataInteger algebra = isoToLeft (alg `ixcata`)
    where
        alg :: NatFunctor (IxTVoid `IxTEither` IxTConst a) :-> IxTConst a
        alg = isoToRight algebra

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

paraFactorial :: Integer -> Integer
paraFactorial = paraInteger $ 1 `maybe` \(n, x) -> n * succ x

