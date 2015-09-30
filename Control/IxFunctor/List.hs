{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

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
        ) where

import Control.IxFunctor.IxFunctor

type ListFunctor = ((IxUnit :+: (IxProj (Left '()) :*: IxProj (Right '()))) :: (Either () () -> *) -> () -> *)

type List = IxFix ListFunctor

fromList :: forall a ix. [a] -> List (IxTConst a) ix
fromList = (coalgebra `ixana`) . IxTConst
    where
        coalgebra :: IxTConst [a] :-> ListFunctor (IxTEither (IxTConst a) (IxTConst [a]))
        coalgebra (IxTConst []) = IxLeft $ from ()
        coalgebra (IxTConst (x : xs)) = IxRight $ from (x, xs)

toList :: forall a ix. List (IxTConst a) ix -> [a]
toList = to . (algebra `ixcata`)
    where
        algebra :: ListFunctor (IxTEither (IxTConst a) (IxTConst [a])) :-> IxTConst [a]
        algebra (IxLeft _) = IxTConst []
        algebra (IxRight xs) = IxTConst (x : xs')
            where
                (x, xs') = to xs

instance Isomorphic [a] (List (IxTConst a) ix) where
    from = fromList

    to = toList

mapList :: (a -> b) -> [a] -> [b]
mapList f = to . (liftIxTConst f `ixmap`) . fromList

cataList :: forall a b. (Either () (b, a) -> a) -> [b] -> a
cataList algebra = isoToLeft (alg `ixcata`)
    where
        alg :: ListFunctor (IxTEither (IxTConst b) (IxTConst a)) :-> IxTConst a
        alg = isoToRight algebra

anaList :: forall a b. (a -> Either () (b, a)) -> a -> [b]
anaList coalgebra = isoToLeft (coalg `ixana`)
    where
        coalg :: IxTConst a :-> ListFunctor (IxTEither (IxTConst b) (IxTConst a))
        coalg = isoToRight coalgebra

hyloList :: forall a b c. (Either () (b, c) -> c) -> (a -> Either () (b, a)) -> a -> c
hyloList algebra coalgebra = isoToLeft $ ixhylo alg coalg
    where
        alg :: ListFunctor (IxTEither (IxTConst b) (IxTConst c)) :-> IxTConst c
        alg = isoToRight algebra
        coalg :: IxTConst a :-> ListFunctor (IxTEither (IxTConst b) (IxTConst a))
        coalg = isoToRight coalgebra

paraList :: forall a b. (Either () (b, (a, [b])) -> a) -> [b] -> a
paraList algebra = isoToLeft (alg `ixpara`)
    where
        alg :: ListFunctor (IxTEither (IxTConst b) (IxTPair (IxTConst a) (List (IxTConst b)))) :-> IxTConst a
        alg = isoToRight algebra

factorial :: Integer -> Integer
factorial = cataList (either (const 1) (uncurry (*))) . anaList coalg
    where
        coalg 0 = Left ()
        coalg n = Right (n, pred n)

hyloFactorial :: Integer -> Integer
hyloFactorial = hyloList (either (const 1) (uncurry (*))) coalg
    where
        coalg 0 = Left ()
        coalg n = Right (n, pred n)

