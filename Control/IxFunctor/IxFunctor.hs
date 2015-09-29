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
        ( Equality(Reflexivity)
        , Isomorphic
        , from
        , to
        , (:->)
        , Void
        , Const(Const)
        , liftConst
        , Union(UnionLeft, UnionRight)
        , split
        , IxFunctor
        , ixmap
        , IxVoid
        , IxUnit(IxUnit)
        , (:+:)(IxLeft, IxRight)
        , (:*:)(IxProd)
        , (:.:)(IxComp)
        , IxProj(IxProj)
        , IxOutUnit(IxOutUnit)
        , IxOut(IxOut)
        , IxFix(IxIn)
        , ixcata
        , ixana
        ) where

data Equality a b where
    Reflexivity :: Equality a a

class Isomorphic a b where
    from :: a -> b

    to :: b -> a

instance Isomorphic a a where
    from = id

    to = id

type t :-> v = forall ix. t ix -> v ix

data Void

data Const :: * -> () -> * where
    Const :: t -> Const t '()

instance Isomorphic a b => Isomorphic a (Const b '()) where
    from = Const . from

    to (Const x) = to x

liftConst :: (t -> v) -> Const t :-> Const v
liftConst f (Const x) = Const $ f x

data Union :: (t -> *) -> (v -> *) -> Either t v -> * where
    UnionLeft :: xf t -> Union xf xg (Left t)
    UnionRight :: xg v -> Union xf xg (Right v)

instance Isomorphic a (b ix) => Isomorphic a (Union b c (Left ix)) where
    from = UnionLeft . from

    to (UnionLeft x) = to x

instance Isomorphic a (c ix) => Isomorphic a (Union b c (Right ix)) where
    from = UnionRight . from

    to (UnionRight x) = to x

split :: (t :-> v) -> (s :-> u) -> Union t s :-> Union v u
split f _ (UnionLeft x) = UnionLeft $ f x
split _ f (UnionRight x) = UnionRight $ f x

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

data IxOutUnit ::
        ((inputIndex -> *) -> () -> *) ->
        (inputIndex -> *) -> () -> * where
    IxOutUnit :: xf r '() -> IxOutUnit xf r '()

instance IxFunctor xf => IxFunctor (IxOutUnit xf) where
    f `ixmap` (IxOutUnit xf) = IxOutUnit $ f `ixmap` xf

instance (IxFunctor xf, Isomorphic a (xf r '())) => Isomorphic a (IxOutUnit xf r '()) where
    from = IxOutUnit . from

    to (IxOutUnit x) = to x

data IxOut :: outputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxOut :: Equality o' o -> IxOut o' r o

instance IxFunctor (IxOut o') where
    _ `ixmap` (IxOut x) = IxOut x

data IxFix ::
        ((Either inputIndex outputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxIn :: IxFunctor xf => xf (Union r (IxFix xf r)) o -> IxFix xf r o

instance IxFunctor (IxFix xf) where
    ixmap :: forall t v. (t :-> v) -> IxFix xf t :-> IxFix xf v
    f `ixmap` (IxIn xf) = IxIn $ f' `ixmap` xf
        where
            f' :: Union t (IxFix xf t) :-> Union v (IxFix xf v)
            f' = f `split` (f `ixmap`)

ixcata :: forall xf r s. IxFunctor xf => xf (Union r s) :-> s -> IxFix xf r :-> s
algebra `ixcata` (IxIn x) = algebra (f `ixmap` x)
    where
        f :: Union r (IxFix xf r) :-> Union r s
        f = id `split` (algebra `ixcata`)

ixana :: forall xf r s. IxFunctor xf => s :-> xf (Union r s) -> s :-> IxFix xf r
coalgebra `ixana` x = IxIn $ f `ixmap` (coalgebra x)
    where
        f :: Union r s :-> Union r (IxFix xf r)
        f = id `split` (coalgebra `ixana`)

