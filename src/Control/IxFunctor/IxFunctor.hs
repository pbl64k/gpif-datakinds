{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE IncoherentInstances #-}

{-|
Module      : Control.IxFunctor.IxFunctor
Description : Indexed functors and functor combinators
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

Functors and combinators used for encoding algebraic data types.
-}

module Control.IxFunctor.IxFunctor
        ( IxFunctor(ixmap)
        , IxVoid
        , IxUnit(IxUnit)
        , (:+:)(IxLeft, IxRight)
        , (:*:)(IxProd)
        , (:.:)(IxComp)
        , IxProj(IxProj)
        , IxOut(IxOut)
        , IxFix(IxFix)
        , ixunfix
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType

-- |Indexed functors map indexed types (and associated arrows) to indexed types.
-- Being parametrized by an indexed type is essentially the same thing as being
-- parametrized by an arbitrary number of type parameters.
class IxFunctor (xf :: (inputIndex -> *) -> outputIndex -> *) where

    -- |Generalizes functorial `fmap`, bifunctorial `bimap` and all n-ary maps
    -- for covariant n-ary functors.
    ixmap :: (t :-> v) -> xf t :-> xf v

-- |Void functor.
data IxVoid :: (inputIndex -> *) -> outputIndex -> *

instance IxFunctor IxVoid where
    _ `ixmap` _ = undefined

instance Isomorphic Void (IxVoid r o) where
    from = undefined

    to = undefined

-- |Unit functor maps everything to unit type.
data IxUnit :: (inputIndex -> *) -> outputIndex -> * where
    IxUnit :: IxUnit r o

instance IxFunctor IxUnit where
    _ `ixmap` _ = IxUnit

instance Isomorphic () (IxUnit r o) where
    from _ = IxUnit

    to _ = ()

-- |Sum of two indexed functors is also an indexed functor.
data (:+:) ::
        ((inputIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxLeft :: (IxFunctor xf, IxFunctor xg) => xf r o -> (xf :+: xg) r o
    IxRight :: (IxFunctor xf, IxFunctor xg) => xg r o -> (xf :+: xg) r o

instance IxFunctor (xf :+: xg) where
    f `ixmap` (IxLeft xf) = IxLeft $ f `ixmap` xf
    f `ixmap` (IxRight xg) = IxRight $ f `ixmap` xg

instance (IxFunctor c, IxFunctor d, Isomorphic a (c r o), Isomorphic b (d r o)) =>
        Isomorphic (a `Either` b) ((c :+: d) r o) where
    from (Left x) = IxLeft $ from x
    from (Right x) = IxRight $ from x

    to (IxLeft x) = Left $ to x
    to (IxRight x) = Right $ to x

instance (IxFunctor c, IxFunctor d, Isomorphic () (c r o), Isomorphic b (d r o)) =>
        Isomorphic (Maybe b) ((c :+: d) r o) where
    from Nothing = IxLeft $ from ()
    from (Just x) = IxRight $ from x

    to (IxLeft _) = Nothing
    to (IxRight x) = Just $ to x

-- |Same with products.
data (:*:) ::
        ((inputIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxProd :: (IxFunctor xf, IxFunctor xg) => xf r o -> xg r o -> (xf :*: xg) r o

instance IxFunctor (xf :*: xg) where
    f `ixmap` (xf `IxProd` xg) = (f `ixmap` xf) `IxProd` (f `ixmap` xg)

instance (IxFunctor c, IxFunctor d, Isomorphic a (c r o), Isomorphic b (d r o)) =>
        Isomorphic (a, b) ((c :*: d) r o) where
    from (a, b) = from a `IxProd` from b

    to (a `IxProd` b) = (to a, to b)

-- |Functors can be composed, subject to unsurprising restrictions on index compatibility.
data (:.:) ::
        ((intermIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> intermIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxComp :: (IxFunctor xf, IxFunctor xg) => xf (xg r) o -> (xf :.: xg) r o

instance IxFunctor (xf :.: xg) where
    ixmap :: (t :-> v) -> (xf :.: xg) t :-> (xf :.: xg) v
    f `ixmap` (IxComp xf) = IxComp $ (f `ixmap`) `ixmap` xf

instance (IxFunctor xf, IxFunctor xg, Isomorphic a (xf (xg r) o)) =>
        Isomorphic a ((xf :.: xg) r o) where
    from = IxComp . from

    to (IxComp x) = to x

-- |Given a certain index and an indexed type, maps all indices to the type
-- yielded by the original indexed type for that index.
data IxProj :: inputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxProj :: r i -> IxProj i r o

instance IxFunctor (IxProj ix) where
    f `ixmap` (IxProj x) = IxProj $ f x

instance Isomorphic a (r i) => Isomorphic a (IxProj i r o) where
    from = IxProj . from

    to (IxProj x) = to x

-- |Only constructible for output index passed as a parameter, barring `fix` `id` 
-- and all that.
data IxOut :: outputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxOut :: Equality o' o -> IxOut o' r o

instance IxFunctor (IxOut o') where
    _ `ixmap` (IxOut x) = IxOut x

-- |Unlike with `Functor`, `Bifunctor` etc., fixed point of an indexed functor
-- is also an indexed functor. `IxFix` uses a specific convention to determine
-- which variables should be treated as free (those tagged as left), and which
-- should be plugged back into the base functor (those tagged as right).
data IxFix ::
        ((Either inputIndex outputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxFix :: IxFunctor xf => xf (r `IxTEither` IxFix xf r) o -> IxFix xf r o

-- |Snips off the `IxFix` data constructor. (`project`, essentially.)
ixunfix :: IxFix xf r o -> xf (r `IxTEither` IxFix xf r) o
ixunfix (IxFix x) = x

instance IxFunctor (IxFix xf) where
    ixmap :: forall t v. (t :-> v) -> IxFix xf t :-> IxFix xf v
    f `ixmap` (IxFix xf) = IxFix $ f' `ixmap` xf
        where
            f' :: IxTEither t (IxFix xf t) :-> IxTEither v (IxFix xf v)
            f' = f `split` (f `ixmap`)

