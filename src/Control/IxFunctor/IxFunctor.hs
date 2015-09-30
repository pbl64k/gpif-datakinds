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

module Control.IxFunctor.IxFunctor
        ( Void
        , Equality(Reflexivity)
        , Isomorphic
        , from
        , to
        , isoToLeft
        , isoToRight
        , (:->)
        , IxTVoid
        , IxTConst(IxTConst)
        , liftIxTConst
        , IxTEither(IxTEitherLeft, IxTEitherRight)
        , split
        , IxTPair(IxTPair)
        , IxFunctor
        , ixmap
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
import Control.IxFunctor.IxType

class IxFunctor (xf :: (inputIndex -> *) -> outputIndex -> *) where
    ixmap :: (t :-> v) -> xf t :-> xf v

data IxVoid :: (inputIndex -> *) -> outputIndex -> *

instance IxFunctor IxVoid where
    _ `ixmap` _ = undefined

instance Isomorphic Void (IxVoid r o) where
    from = undefined

    to = undefined

data IxUnit :: (inputIndex -> *) -> outputIndex -> * where
    IxUnit :: IxUnit r o

instance IxFunctor IxUnit where
    _ `ixmap` _ = IxUnit

instance Isomorphic () (IxUnit r o) where
    from _ = IxUnit

    to _ = ()

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

data IxProj :: inputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxProj :: r i -> IxProj i r o

instance IxFunctor (IxProj ix) where
    f `ixmap` (IxProj x) = IxProj $ f x

instance Isomorphic a (r i) => Isomorphic a (IxProj i r o) where
    from = IxProj . from

    to (IxProj x) = to x

data IxOut :: outputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxOut :: Equality o' o -> IxOut o' r o

instance IxFunctor (IxOut o') where
    _ `ixmap` (IxOut x) = IxOut x

data IxFix ::
        ((Either inputIndex outputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxFix :: IxFunctor xf => xf (r `IxTEither` IxFix xf r) o -> IxFix xf r o

ixunfix :: IxFix xf r o -> xf (r `IxTEither` IxFix xf r) o
ixunfix (IxFix x) = x

instance IxFunctor (IxFix xf) where
    ixmap :: forall t v. (t :-> v) -> IxFix xf t :-> IxFix xf v
    f `ixmap` (IxFix xf) = IxFix $ f' `ixmap` xf
        where
            f' :: IxTEither t (IxFix xf t) :-> IxTEither v (IxFix xf v)
            f' = f `split` (f `ixmap`)

