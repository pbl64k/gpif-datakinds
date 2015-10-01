{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Control.IxFunctor.EvenOdd
        ( Even(ENil, ECons)
        , Odd(OCons)
        , EvenOddFunctor
        , EvenOdd
        , fromEven
        , fromOdd
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme

data Even a b = ENil | ECons a (Odd a b) deriving Show

data Odd a b = OCons b (Even a b) deriving Show

type EO a b = Either (Even a b) (Odd a b)

type EvenOddFunctor =
        (((IxOut (Left '()) :*: (IxUnit :+: (IxProj (Left (Left '())) :*: IxProj (Right (Right '())))))
        :+:
        (IxOut (Right '()) :*: (IxProj (Left (Right '())) :*: IxProj (Right (Left '())))))
        :: (Either (Either () ()) (Either () ()) -> *) -> Either () () -> *)

type EvenOdd = IxFix EvenOddFunctor

fromEven :: forall a b c d. (Isomorphic a (c '()), Isomorphic b (d '())) =>
        Even a b -> EvenOdd (c `IxTEither` d) (Left '())
fromEven ENil = IxFix $ IxLeft $ IxOut Reflexivity `IxProd` IxLeft (from ())
fromEven (ECons x xs) = IxFix $ IxLeft $ IxOut Reflexivity `IxProd` IxRight (from x `IxProd` IxProj (IxTEitherRight (fromOdd xs)))

fromOdd :: forall a b c d. (Isomorphic a (c '()), Isomorphic b (d '())) =>
        Odd a b -> EvenOdd (c `IxTEither` d) (Right '())
fromOdd (OCons x xs) = IxFix $ IxRight $ IxOut Reflexivity `IxProd` (from x `IxProd` IxProj (IxTEitherRight (fromEven xs)))

