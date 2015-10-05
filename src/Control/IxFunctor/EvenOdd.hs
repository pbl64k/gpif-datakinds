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
Module      : Control.IxFunctor.EvenOdd
Description : Even-odd lists
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

A contrived example demonstrating the encoding of families of mutually recursive data types
and multiple type parameters. Since even the concrete instantiations of anamorphisms have grown
to be quite complicated, unwieldy and impractical, I'm omitting hylos, apos and all that zoo
for fear of my own sanity.
-}

module Control.IxFunctor.EvenOdd
        ( Even(ENil, ECons)
        , Odd(OCons)
        , EvenOddFunctor
        , EvenOdd
        , fromEven
        , fromOdd
        , toEven
        , toOdd
        , mapEven
        , mapOdd
        , cataEven
        , cataOdd
        , anaEven
        , anaOdd
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme

data Even a b = ENil | ECons a (Odd a b) deriving Show

data Odd a b = OCons b (Even a b) deriving Show

-- |Base functor for even-odd lists. Uses `IxOut` to enforce the invariant.
type EvenOddFunctor =
        (((IxOut (Left '()) :*: (IxUnit :+: (IxProj (Left (Left '())) :*: IxProj (Right (Right '())))))
        :+:
        (IxOut (Right '()) :*: (IxProj (Left (Right '())) :*: IxProj (Right (Left '())))))
        :: (Either (Either () ()) (Either () ()) -> *) -> Either () () -> *)

-- |Indexed functor accepting two type parameters (in form of an indexed type)
-- and producing a family of two mutually recursive types isomorphic to `Even`
-- and `Odd` above.
type EvenOdd = IxFix EvenOddFunctor

fromEven :: forall a b c d. (Isomorphic a (c '()), Isomorphic b (d '())) =>
        Even a b -> EvenOdd (c `IxTEither` d) (Left '())
fromEven ENil = IxFix $ IxLeft $ IxOut Reflexivity `IxProd` IxLeft (from ())
fromEven (ECons x xs) = IxFix $ IxLeft $ IxOut Reflexivity `IxProd` IxRight (from x `IxProd` IxProj (IxTEitherRight (fromOdd xs)))

fromOdd :: forall a b c d. (Isomorphic a (c '()), Isomorphic b (d '())) =>
        Odd a b -> EvenOdd (c `IxTEither` d) (Right '())
fromOdd (OCons x xs) = IxFix $ IxRight $ IxOut Reflexivity `IxProd` (from x `IxProd` IxProj (IxTEitherRight (fromEven xs)))

toEven :: forall a b c d. (Isomorphic a (c '()), Isomorphic b (d '())) =>
        EvenOdd (c `IxTEither` d) (Left '()) -> Even a b
toEven (IxFix (IxLeft (IxOut Reflexivity `IxProd` IxLeft _))) = ENil
toEven (IxFix (IxLeft (IxOut Reflexivity `IxProd` IxRight (x `IxProd` IxProj (IxTEitherRight xs))))) = ECons (to x) (toOdd xs)

toOdd :: forall a b c d. (Isomorphic a (c '()), Isomorphic b (d '())) =>
        EvenOdd (c `IxTEither` d) (Right '()) -> Odd a b
toOdd (IxFix (IxRight (IxOut Reflexivity `IxProd` (x `IxProd` IxProj (IxTEitherRight xs))))) = OCons (to x) (toEven xs)

instance (Isomorphic a (c '()), Isomorphic b (d '())) =>
        Isomorphic (Even a b) (EvenOdd (c `IxTEither` d) (Left '())) where
    from = fromEven

    to = toEven

instance (Isomorphic a (c '()), Isomorphic b (d '())) =>
        Isomorphic (Odd a b) (EvenOdd (c `IxTEither` d) (Right '())) where
    from = fromOdd

    to = toOdd

mapEven :: forall a b c d. (a -> c) -> (b -> d) -> Even a b -> Even c d
mapEven f g = toEven . ((liftIxTConst f `split` liftIxTConst g) `ixmap`) . fromEven

mapOdd :: forall a b c d. (a -> c) -> (b -> d) -> Odd a b -> Odd c d
mapOdd f g = toOdd . ((liftIxTConst f `split` liftIxTConst g) `ixmap`) . fromOdd

cataEven :: forall a b c d. (Maybe (a, d) -> c) -> ((b, c) -> d) -> Even a b -> c
cataEven algEven algOdd xs = res'
    where
        alg :: EvenOddFunctor ((IxTConst a `IxTEither` IxTConst b) `IxTEither` (IxTConst c `IxTEither` IxTConst d)) :->
                (IxTConst c `IxTEither` IxTConst d)
        alg (IxLeft (IxOut Reflexivity `IxProd` xs)) = IxTEitherLeft $ isoToRight algEven xs
        alg (IxRight (IxOut Reflexivity `IxProd` xs)) = IxTEitherRight $ isoToRight algOdd xs
        res = alg `ixcata` fromEven xs
        res' :: c
        res' = case res of (IxTEitherLeft (IxTConst res)) -> res

cataOdd :: forall a b c d. (Maybe (a, d) -> c) -> ((b, c) -> d) -> Odd a b -> d
cataOdd algEven algOdd xs = res'
    where
        alg :: EvenOddFunctor ((IxTConst a `IxTEither` IxTConst b) `IxTEither` (IxTConst c `IxTEither` IxTConst d)) :->
                (IxTConst c `IxTEither` IxTConst d)
        alg (IxLeft (IxOut Reflexivity `IxProd` xs)) = IxTEitherLeft $ isoToRight algEven xs
        alg (IxRight (IxOut Reflexivity `IxProd` xs)) = IxTEitherRight $ isoToRight algOdd xs
        res = alg `ixcata` fromOdd xs
        res' :: d
        res' = case res of (IxTEitherRight (IxTConst res)) -> res

anaEven :: forall a b c d. (c -> Maybe (a, d)) -> (d -> (b, c)) -> c -> Even a b
anaEven coalgEven coalgOdd x = toEven res
    where
        coalg :: forall (ix :: Either () ()).
                ((IxOut (Left '()) :*: IxProj (Left '())) :+: (IxOut (Right '()) :*: IxProj (Right '()))) (IxTConst c `IxTEither` IxTConst d) ix ->
                EvenOddFunctor ((IxTConst a `IxTEither` IxTConst b) `IxTEither` (((IxOut (Left '()) :*: IxProj (Left '())) :+: (IxOut (Right '()) :*: IxProj (Right '()))) (IxTConst c `IxTEither` IxTConst d))) ix
        coalg (IxLeft (IxOut refl `IxProd` x)) = IxLeft $ IxOut refl `IxProd` seed'
            where
                x' = coalgEven $ to x
                seed' = case x' of
                    Nothing -> IxLeft IxUnit
                    Just (a, b) -> IxRight $ IxProj (from a) `IxProd` IxProj (IxTEitherRight (IxRight (IxOut Reflexivity `IxProd` IxProj (from b))))
        coalg (IxRight (IxOut refl `IxProd` x)) = IxRight $ IxOut refl `IxProd` seed'
            where
                (a, b) = coalgOdd $ to x
                seed' = IxProj (from a) `IxProd` IxProj (IxTEitherRight (IxLeft (IxOut Reflexivity `IxProd` IxProj (from b))))
        x' :: ((IxOut (Left '()) :*: IxProj (Left '())) :+: (IxOut (Right '()) :*: IxProj (Right '())))
                (IxTConst c `IxTEither` IxTConst d) (Left '())
        x' = IxLeft $ IxOut Reflexivity `IxProd` IxProj (IxTEitherLeft (IxTConst x))
        res :: EvenOdd (IxTConst a `IxTEither` IxTConst b) (Left '())
        res = coalg `ixana` x'

anaOdd :: forall a b c d. (c -> Maybe (a, d)) -> (d -> (b, c)) -> d -> Odd a b
anaOdd coalgEven coalgOdd x = toOdd res
    where
        coalg :: forall (ix :: Either () ()).
                ((IxOut (Left '()) :*: IxProj (Left '())) :+: (IxOut (Right '()) :*: IxProj (Right '()))) (IxTConst c `IxTEither` IxTConst d) ix ->
                EvenOddFunctor ((IxTConst a `IxTEither` IxTConst b) `IxTEither` (((IxOut (Left '()) :*: IxProj (Left '())) :+: (IxOut (Right '()) :*: IxProj (Right '()))) (IxTConst c `IxTEither` IxTConst d))) ix
        coalg (IxLeft (IxOut refl `IxProd` x)) = IxLeft $ IxOut refl `IxProd` seed'
            where
                x' = coalgEven $ to x
                seed' = case x' of
                    Nothing -> IxLeft IxUnit
                    Just (a, b) -> IxRight $ IxProj (from a) `IxProd` IxProj (IxTEitherRight (IxRight (IxOut Reflexivity `IxProd` IxProj (from b))))
        coalg (IxRight (IxOut refl `IxProd` x)) = IxRight $ IxOut refl `IxProd` seed'
            where
                (a, b) = coalgOdd $ to x
                seed' = IxProj (from a) `IxProd` IxProj (IxTEitherRight (IxLeft (IxOut Reflexivity `IxProd` IxProj (from b))))
        x' :: ((IxOut (Left '()) :*: IxProj (Left '())) :+: (IxOut (Right '()) :*: IxProj (Right '())))
                (IxTConst c `IxTEither` IxTConst d) (Right '())
        x' = IxRight $ IxOut Reflexivity `IxProd` IxProj (IxTEitherRight (IxTConst x))
        res :: EvenOdd (IxTConst a `IxTEither` IxTConst b) (Right '())
        res = coalg `ixana` x'

