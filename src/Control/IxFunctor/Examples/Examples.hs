
{-|
Module      : Control.IxFunctor.Examples.Examples
Description : A bunch of fairly trivial examples
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

-}

module Control.IxFunctor.Examples.Examples
        ( paraFactorial
        , anacataFactorial
        , hyloFactorial
        , sumList
        , sumTree
        , sumEven
        , genEven
        , RoseTree(RoseTree)
        , Even(ENil, ECons)
        , Odd(OCons)
        ) where

import Control.IxFunctor.Nat
import Control.IxFunctor.List
import Control.IxFunctor.Rose
import Control.IxFunctor.EvenOdd

-- |Factorial as a paramorphism on nats.
paraFactorial :: Integer -> Integer
paraFactorial = paraInteger $ 1 `maybe` \(n, x) -> n * succ x

-- |Factorial as a hylomorphism on lists.
anacataFactorial :: Integer -> Integer
anacataFactorial = cataList (1 `maybe` uncurry (*)) . anaList coalg
    where
        coalg 0 = Nothing
        coalg n = Just (n, pred n)

-- |Same, but with explicit appeal to hylo.
hyloFactorial :: Integer -> Integer
hyloFactorial = hyloList (1 `maybe` uncurry (*)) coalg
    where
        coalg 0 = Nothing
        coalg n = Just (n, pred n)

sumList :: Num a => [a] -> a
sumList = cataList (0 `maybe` uncurry (+))

sumTree :: Num a => RoseTree a -> a
sumTree = cataRose (\(x, xs) -> x + sumList xs)

sumEven :: Even Integer String -> Integer
sumEven = cataEven (0 `maybe` uncurry (+)) (\(x, y) -> read x + y)

genEven :: Integer -> Even Integer Integer
genEven = anaEven (\x -> if x <= 0 then Nothing else Just (x, pred x)) (\x -> (x, pred x))

