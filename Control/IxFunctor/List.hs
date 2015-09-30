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

fromList :: forall a ix. [a] -> List (Const a) ix
fromList = (coalgebra `ixana`) . Const
    where
        coalgebra :: Const [a] :-> ListFunctor (Union (Const a) (Const [a]))
        coalgebra (Const []) = IxLeft $ from ()
        coalgebra (Const (x : xs)) = IxRight $ from (x, xs)

toList :: forall a ix. List (Const a) ix -> [a]
toList = to . (algebra `ixcata`)
    where
        algebra :: ListFunctor (Union (Const a) (Const [a])) :-> Const [a]
        algebra (IxLeft _) = Const []
        algebra (IxRight xs) = Const (x : xs')
            where
                (x, xs') = to xs

instance Isomorphic [a] (List (Const a) ix) where
    from = fromList

    to = toList

mapList :: (a -> b) -> [a] -> [b]
mapList f = to . (liftConst f `ixmap`) . fromList

cataList :: forall a b. (Either () (b, a) -> a) -> [b] -> a
cataList algebra = isoToLeft (alg `ixcata`)
    where
        alg :: ListFunctor (Union (Const b) (Const a)) :-> Const a
        alg = isoToRight algebra

anaList :: forall a b. (a -> Either () (b, a)) -> a -> [b]
anaList coalgebra = isoToLeft (coalg `ixana`)
    where
        coalg :: Const a :-> ListFunctor (Union (Const b) (Const a))
        coalg = isoToRight coalgebra

hyloList :: forall a b c. (Either () (b, c) -> c) -> (a -> Either () (b, a)) -> a -> c
hyloList algebra coalgebra = isoToLeft $ ixhylo alg coalg
    where
        alg :: ListFunctor (Union (Const b) (Const c)) :-> Const c
        alg = isoToRight algebra
        coalg :: Const a :-> ListFunctor (Union (Const b) (Const a))
        coalg = isoToRight coalgebra

paraList :: forall a b. (Either () (b, (a, [b])) -> a) -> [b] -> a
paraList algebra = isoToLeft (alg `ixpara`)
    where
        alg :: ListFunctor (Union (Const b) (ParamPair (Const a) (List (Const b)))) :-> Const a
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

