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
        , IxTPair
        , IxFunctor
        , ixmap
        , IxVoid
        , IxUnit(IxUnit)
        , (:+:)(IxLeft, IxRight)
        , (:*:)(IxProd)
        , (:.:)(IxComp)
        , IxProj(IxProj)
        , IxOut(IxOut)
        , IxFix(IxIn)
        , ixcata
        , ixana
        , ixhylo
        , ixmeta
        , ixpara
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
        Isomorphic (Either a b) ((c :+: d) r o) where
    from (Left x) = IxLeft $ from x
    from (Right x) = IxRight $ from x

    to (IxLeft x) = Left $ to x
    to (IxRight x) = Right $ to x

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
    IxIn :: IxFunctor xf => xf (IxTEither r (IxFix xf r)) o -> IxFix xf r o

instance IxFunctor (IxFix xf) where
    ixmap :: forall t v. (t :-> v) -> IxFix xf t :-> IxFix xf v
    f `ixmap` (IxIn xf) = IxIn $ f' `ixmap` xf
        where
            f' :: IxTEither t (IxFix xf t) :-> IxTEither v (IxFix xf v)
            f' = f `split` (f `ixmap`)

ixcata :: forall xf r s. IxFunctor xf => xf (IxTEither r s) :-> s -> IxFix xf r :-> s
algebra `ixcata` (IxIn x) = algebra (f `ixmap` x)
    where
        f :: IxTEither r (IxFix xf r) :-> IxTEither r s
        f = id `split` (algebra `ixcata`)

ixana :: forall xf r s. IxFunctor xf => s :-> xf (IxTEither r s) -> s :-> IxFix xf r
coalgebra `ixana` x = IxIn $ f `ixmap` (coalgebra x)
    where
        f :: IxTEither r s :-> IxTEither r (IxFix xf r)
        f = id `split` (coalgebra `ixana`)

ixhylo :: forall xf r s t. IxFunctor xf =>
        xf (IxTEither r t) :-> t -> s :-> xf (IxTEither r s) -> s :-> t
ixhylo algebra coalgebra = algebra . (f `ixmap`) . coalgebra
    where
        f :: IxTEither r s :-> IxTEither r t
        f = id `split` (ixhylo algebra coalgebra)

ixmeta :: forall xf xg r s t. (IxFunctor xf, IxFunctor xg) =>
        s :-> xg (IxTEither t s) -> xf (IxTEither r s) :-> s -> IxFix xf r :-> IxFix xg t
-- Oh, who cares...
ixmeta coalgebra algebra = (coalgebra `ixana`) . (algebra `ixcata`)

ixpara :: forall xf r s. xf (IxTEither r (IxTPair s (IxFix xf r))) :-> s -> IxFix xf r :-> s
algebra `ixpara` (IxIn x) = algebra (f `ixmap` x)
    where
        fanout f g x = f x `IxTPair` g x
        f :: IxTEither r (IxFix xf r) :-> IxTEither r (IxTPair s (IxFix xf r))
        f = id `split` ((algebra `ixpara`) `fanout` id)

--ixapo :: forall xf r s. s :-> xf (IxTEither r (IxTEither s (IxFix xf r))) -> s :-> IxFix xf r
--coalgebra `ixapo` x = IxIn $ _ `ixmap` (coalgebra x)

