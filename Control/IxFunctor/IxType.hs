{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE IncoherentInstances #-}

module Control.IxFunctor.IxType
        ( Isomorphic
        , from
        , to
        , isoToLeft
        , isoToRight
        , Void
        , (:->)
        , IxTVoid(IxTVoid)
        , IxTConst(IxTConst)
        , liftIxTConst
        , IxTEither(IxTEitherLeft, IxTEitherRight)
        , split
        , IxTPair(IxTPair)
        ) where

import Control.IxFunctor.Iso

data Void = Void

type t :-> v = forall ix. t ix -> v ix

data IxTVoid :: Void -> * where
    IxTVoid :: IxTVoid 'Void

data IxTConst :: * -> () -> * where
    IxTConst :: t -> IxTConst t ix

instance Isomorphic a b => Isomorphic a (IxTConst b ix) where
    from = IxTConst . from

    to (IxTConst x) = to x

liftIxTConst :: (t -> v) -> IxTConst t :-> IxTConst v
liftIxTConst f (IxTConst x) = IxTConst $ f x

data IxTEither :: (t -> *) -> (v -> *) -> Either t v -> * where
    IxTEitherLeft :: tf t -> IxTEither tf tg (Left t)
    IxTEitherRight :: tg v -> IxTEither tf tg (Right v)

instance Isomorphic a (b ix) => Isomorphic a (IxTEither b c (Left ix)) where
    from = IxTEitherLeft . from

    to (IxTEitherLeft x) = to x

instance Isomorphic a (c ix) => Isomorphic a (IxTEither b c (Right ix)) where
    from = IxTEitherRight . from

    to (IxTEitherRight x) = to x

split :: (t :-> v) -> (s :-> u) -> IxTEither t s :-> IxTEither v u
split f _ (IxTEitherLeft x) = IxTEitherLeft $ f x
split _ f (IxTEitherRight x) = IxTEitherRight $ f x

data IxTPair :: (t -> *) -> (t -> *) -> t -> * where
    IxTPair :: xf t -> xg t -> IxTPair xf xg t

instance (Isomorphic a (c ix), Isomorphic b (d ix)) => Isomorphic (a, b) (IxTPair c d ix) where
    from (x, y) = from x `IxTPair` from y

    to (IxTPair x y) = (to x, to y)

