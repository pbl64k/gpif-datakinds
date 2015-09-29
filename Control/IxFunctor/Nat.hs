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
        ) where

import Control.IxFunctor.IxFunctor

type NatFunctor = IxOutUnit (IxUnit :+: IxProj (Right '()))

type Nat = IxFix NatFunctor

fromIntegerToNat :: Integer -> Nat (Const Void) '()
fromIntegerToNat = (coalgebra `ixana`) . Const
    where
        coalgebra :: Const Integer :-> NatFunctor (Union (Const Void) (Const Integer))
        coalgebra (Const 0) = IxOutUnit $ IxLeft IxUnit
        coalgebra (Const n) = IxOutUnit $ IxRight $ from $ pred n

toIntegerFromNat :: Nat (Const Void) '() -> Integer
toIntegerFromNat = to . (algebra `ixcata`)
    where
        algebra :: NatFunctor (Union (Const Void) (Const Integer)) :-> Const Integer
        algebra (IxOutUnit (IxLeft _)) = Const 0
        algebra (IxOutUnit (IxRight x)) = Const $ succ $ to x

instance Isomorphic Integer (Nat (Const Void) '()) where
    from = fromIntegerToNat

    to = toIntegerFromNat

cataInteger :: forall a. (Either () a -> a) -> Integer -> a
cataInteger algebra = to . (alg `ixcata`) . fromIntegerToNat
    where
        alg :: NatFunctor (Union (Const Void) (Const a)) :-> Const a
        alg (IxOutUnit x) = from $ algebra $ to x

anaInteger :: forall a. (a -> Either () a) -> a -> Integer
anaInteger coalgebra = toIntegerFromNat . (coalg `ixana`) . from
    where
        coalg :: Const a :-> NatFunctor (Union (Const Void) (Const a))
        coalg (Const x) = from $ coalgebra x

