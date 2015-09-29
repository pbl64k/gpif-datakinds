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

type ListFunctor = IxOutUnit (IxUnit :+: (IxProj (Left '()) :*: IxProj (Right '())))

type List = IxFix ListFunctor

fromList :: forall a. [a] -> List (Const a) '()
fromList = (coalgebra `ixana`) . Const
    where
        coalgebra :: Const [a] :-> ListFunctor (Union (Const a) (Const [a]))
        coalgebra (Const []) = IxOutUnit $ IxLeft IxUnit
        coalgebra (Const (x : xs)) = IxOutUnit $ IxRight $ from (x, xs)

toList :: forall a. List (Const a) '() -> [a]
toList = to . (algebra `ixcata`)
    where
        algebra :: ListFunctor (Union (Const a) (Const [a])) :-> Const [a]
        algebra (IxOutUnit (IxLeft _)) = Const []
        algebra (IxOutUnit (IxRight xs)) = Const (x : xs')
            where
                (x, xs') = to xs

instance Isomorphic [a] (List (Const a) '()) where
    from = fromList

    to = toList

mapList :: (a -> b) -> [a] -> [b]
mapList f = to . (liftConst f `ixmap`) . fromList

cataList :: forall a b. (Either () (b, a) -> a) -> [b] -> a
cataList algebra = to . (alg `ixcata`) . fromList
    where
        alg :: ListFunctor (Union (Const b) (Const a)) :-> Const a
        alg (IxOutUnit x) = from $ algebra $ to x

anaList :: forall a b. (a -> Either () (b, a)) -> a -> [b]
anaList coalgebra = toList . (coalg `ixana`) . from
    where
        coalg :: Const a :-> ListFunctor (Union (Const b) (Const a))
        coalg (Const x) = from $ coalgebra x

hyloList :: forall a b c. (Either () (b, c) -> c) -> (a -> Either () (b, a)) -> a -> c
hyloList algebra coalgebra = to . ixhylo alg coalg . Const
    where
        alg :: ListFunctor (Union (Const b) (Const c)) :-> Const c
        alg (IxOutUnit x) = from $ algebra $ to x
        coalg :: Const a :-> ListFunctor (Union (Const b) (Const a))
        coalg (Const x) = from $ coalgebra x

paraList :: forall a b. (Either () (b, (a, [b])) -> a) -> [b] -> a
paraList algebra = to . (alg `ixpara`) . fromList
    where
        alg :: ListFunctor (Union (Const b) (ParamPair (Const a) (List (Const b)))) :-> Const a
        alg (IxOutUnit x) = from $ algebra $ to x

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

