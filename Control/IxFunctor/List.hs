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

factorial :: Integer -> Integer
factorial = cataList (either (const 1) (uncurry (*))) . anaList coalg
    where
        coalg 0 = Left ()
        coalg n = Right (n, pred n)

