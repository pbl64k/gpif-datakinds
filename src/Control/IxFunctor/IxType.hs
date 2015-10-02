{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE IncoherentInstances #-}

{-|
Module      : Control.IxFunctor.IxType
Description : Indexed types and combinators
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

Basic indexed types and combinators used as building blocks.
-}

module Control.IxFunctor.IxType
        ( Void
        , (:->)
        , IxTVoid
        , IxTConst(IxTConst)
        , liftIxTConst
        , IxTEither(IxTEitherLeft, IxTEitherRight)
        , split
        , IxTTuple(IxTTuple)
        , IxTChoice(IxTChoiceLeft, IxTChoiceRight)
        , IxTPair(IxTPair)
        ) where

import Control.IxFunctor.Iso

-- |Uninhabited type (except for `undefined`).
data Void

-- |An arrow type between indexed types with the same index domain.
type t :-> v = forall ix. t ix -> v ix

-- |Void indexed type.
data IxTVoid :: Void -> * where

-- |Constant indexed type that maps to the same type for all indices in the
-- domain.
data IxTConst :: * -> ix -> * where
    IxTConst :: t -> IxTConst t ix

instance Isomorphic a b => Isomorphic a (IxTConst b ix) where
    from = IxTConst . from

    to (IxTConst x) = to x

-- |Lifts a given function to an arrow operating on corresponding constant
-- indexed types.
liftIxTConst :: (t -> v) -> IxTConst t :-> IxTConst v
liftIxTConst f (IxTConst x) = IxTConst $ f x

-- |Given two indexed types, produces a type indexed by a tagged sum of the
-- two original domains.
data IxTEither :: (t -> *) -> (v -> *) -> Either t v -> * where
    IxTEitherLeft :: tf t -> IxTEither tf tg (Left t)
    IxTEitherRight :: tg v -> IxTEither tf tg (Right v)

instance Isomorphic a (b ix) => Isomorphic a (IxTEither b c (Left ix)) where
    from = IxTEitherLeft . from

    to (IxTEitherLeft x) = to x

instance Isomorphic a (c ix) => Isomorphic a (IxTEither b c (Right ix)) where
    from = IxTEitherRight . from

    to (IxTEitherRight x) = to x

-- |Given two arrows, maps left indices with the first arrow and right indices
-- with the second arrow.
split :: (t :-> v) -> (s :-> u) -> IxTEither t s :-> IxTEither v u
split f _ (IxTEitherLeft x) = IxTEitherLeft $ f x
split _ f (IxTEitherRight x) = IxTEitherRight $ f x

-- |Similar to `IxTEither`, but uses a product of domains.
data IxTTuple :: (t -> *) -> (v -> *) -> (t, v) -> * where
    IxTTuple :: tf t -> tg v -> IxTTuple tf tg '(t, v)

instance (Isomorphic a (c ix), Isomorphic b (d jx)) => Isomorphic (a, b) (IxTTuple c d '(ix, jx)) where
    from (x, y) = from x `IxTTuple` from y

    to (x `IxTTuple` y) = (to x, to y)

-- |Given two types with the same index domain, produces a type with the same
-- domain with values being sums of all mapped types.
data IxTChoice :: (t -> *) -> (t -> *) -> t -> * where
    IxTChoiceLeft :: tf t -> IxTChoice tf tg t
    IxTChoiceRight :: tg t -> IxTChoice tf tg t

instance (Isomorphic a (c ix), Isomorphic b (d ix)) => Isomorphic (Either a b) (IxTChoice c d ix) where
    from (Left x) = IxTChoiceLeft $ from x
    from (Right x) = IxTChoiceRight $ from x

    to (IxTChoiceLeft x) = Left $ to x
    to (IxTChoiceRight x) = Right $ to x

-- |Similar to `IxTChoice`, but yields product of all mapped types.
data IxTPair :: (t -> *) -> (t -> *) -> t -> * where
    IxTPair :: xf t -> xg t -> IxTPair xf xg t

instance (Isomorphic a (c ix), Isomorphic b (d ix)) => Isomorphic (a, b) (IxTPair c d ix) where
    from (x, y) = from x `IxTPair` from y

    to (x `IxTPair` y) = (to x, to y)

