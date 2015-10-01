{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}

module Control.IxFunctor.Rose
        ( RoseFunctor
        , Rose
        , fromRose
        , toRose
        , mapRose
        , cataRose
        --, anaRose
        --, hyloRose
        --, paraRose
        --, apoRose
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor
import Control.IxFunctor.RecScheme
import Control.IxFunctor.List

--instance Show (a ix) => Show (IxTEither a b (Left ix)) where
--    show (IxTEitherLeft x) = "IxTEitherLeft " ++ show x
--
--instance Show (b ix) => Show (IxTEither a b (Right ix)) where
--    show (IxTEitherRight x) = "IxTEitherRight " ++ show x
--
--deriving instance Show (Equality a b)
--deriving instance Show a => Show (IxTConst a ix)
--deriving instance Show (IxVoid r o)
--deriving instance Show (IxUnit r o)
--deriving instance (Show (a r o), Show (b r o)) => Show ((a :+: b) r o)
--deriving instance (Show (a r o), Show (b r o)) => Show ((a :*: b) r o)
--deriving instance Show (a (b r) o) => Show ((a :.: b) r o)
--deriving instance Show (r i) => Show (IxProj i r o)
--deriving instance Show (IxOut o' r o)
--deriving instance Show (a (IxTEither r (IxFix a r)) o) => Show (IxFix a r o)

data RoseTree a = RoseTree a [RoseTree a] deriving Show

type RoseFunctor = ((IxProj (Left '()) :*: (List :.: IxProj (Right '()))) :: (Either () () -> *) -> () -> *)

type Rose = IxFix RoseFunctor

fromRose :: forall a b ix. Isomorphic a (b '()) => RoseTree a -> Rose b ix
fromRose = (coalgebra `ixana`) . from
    where
        coalgebra :: forall ix. IxTConst (RoseTree a) ix -> RoseFunctor (b `IxTEither` IxTConst (RoseTree a)) ix
        coalgebra (IxTConst (RoseTree x xs)) = from x `IxProd` from xs

toRose :: forall a b ix. Isomorphic a (b '()) => Rose b ix -> RoseTree a
toRose = to . (algebra `ixcata`)
    where
        algebra :: forall ix. RoseFunctor (b `IxTEither` IxTConst (RoseTree a)) ix -> IxTConst (RoseTree a) ix
        algebra (x `IxProd` xs) = IxTConst $ RoseTree (to x) (to xs)

instance Isomorphic a (b '()) => Isomorphic (RoseTree a) (Rose b ix) where
    from = fromRose

    to = toRose

mapRose :: (a -> b) -> RoseTree a -> RoseTree b
mapRose f = toRose . (liftIxTConst f `ixmap`) . fromRose

cataRose :: forall a b. ((a, [b]) -> b) -> RoseTree a -> b
cataRose algebra = isoToLeft (alg `ixcata`)
    where
        alg :: RoseFunctor (IxTConst a `IxTEither` IxTConst b) :-> IxTConst b
        alg = isoToRight algebra

