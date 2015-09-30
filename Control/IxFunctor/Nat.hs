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

import Control.IxFunctor.IxFunctor

type NatFunctor = ((IxUnit :+: IxProj (Right '())) :: (Either Void () -> *) -> () -> *)

type Nat = IxFix NatFunctor

fromIntegerToNat :: Integer -> Nat IxTVoid ix
fromIntegerToNat = (coalgebra `ixana`) . IxTConst
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

cataInteger :: forall a. (() `Either` a -> a) -> Integer -> a
cataInteger algebra = isoToLeft (alg `ixcata`)
    where
        alg :: NatFunctor (IxTVoid `IxTEither` IxTConst a) :-> IxTConst a
        alg = isoToRight algebra

anaInteger :: forall a. (a -> () `Either` a) -> a -> Integer
anaInteger coalgebra = isoToLeft (coalg `ixana`)
    where
        coalg :: IxTConst a :-> NatFunctor (IxTVoid `IxTEither` IxTConst a)
        coalg = isoToRight coalgebra

hyloInteger :: forall a b. (() `Either` b -> b) -> (a -> () `Either` a) -> a -> b
hyloInteger algebra coalgebra = isoToLeft $ ixhylo alg coalg
    where
        alg :: NatFunctor (IxTVoid `IxTEither` IxTConst b) :-> IxTConst b
        alg = isoToRight algebra
        coalg :: IxTConst a :-> NatFunctor (IxTVoid `IxTEither` (IxTConst a))
        coalg = isoToRight coalgebra

paraInteger :: forall a. (() `Either` (a, Integer) -> a) -> Integer -> a
paraInteger algebra = isoToLeft (alg `ixpara`)
    where
        alg :: NatFunctor (IxTVoid `IxTEither` (IxTConst a `IxTPair` Nat IxTVoid)) :-> IxTConst a
        alg = isoToRight algebra

paraFactorial :: Integer -> Integer
paraFactorial = paraInteger $ either (const 1) (\(n, x) -> n * succ x)

