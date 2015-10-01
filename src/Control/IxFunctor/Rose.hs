{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Control.IxFunctor.Rose
        ( RoseFunctor
        , Rose
        , fromRose
        , toRose
        , mapRose
        --, cataRose
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

instance Show (a ix) => Show (IxTEither a b (Left ix)) where
    show (IxTEitherLeft x) = "IxTEitherLeft " ++ show x

instance Show (b ix) => Show (IxTEither a b (Right ix)) where
    show (IxTEitherRight x) = "IxTEitherRight " ++ show x

deriving instance Show (Equality a b)
deriving instance Show a => Show (IxTConst a ix)
deriving instance Show (IxVoid r o)
deriving instance Show (IxUnit r o)
deriving instance (Show (a r o), Show (b r o)) => Show ((a :+: b) r o)
deriving instance (Show (a r o), Show (b r o)) => Show ((a :*: b) r o)
deriving instance Show (a (b r) o) => Show ((a :.: b) r o)
deriving instance Show (r i) => Show (IxProj i r o)
deriving instance Show (IxOut o' r o)
deriving instance Show (a (IxTEither r (IxFix a r)) o) => Show (IxFix a r o)

data RoseTree a = RoseTree a [RoseTree a] deriving Show

type RoseFunctor = ((IxProj (Left '()) :*: (List :.: IxProj (Right '()))) :: (Either () () -> *) -> () -> *)

type Rose = IxFix RoseFunctor

fromRose :: forall a ix. RoseTree a -> Rose (IxTConst a) ix
fromRose = (coalgebra `ixana`) . from
    where
        coalgebra :: forall ix. IxTConst (RoseTree a) ix -> RoseFunctor (IxTConst a `IxTEither` IxTConst (RoseTree a)) ix
        coalgebra (IxTConst (RoseTree x xs)) = from (x, conv `ixmap` xs')
            where
                xs' :: List (IxTConst (RoseTree a)) ix
                xs' = fromList xs
                f :: RoseTree a -> IxProj (Right '()) (IxTConst a `IxTEither` IxTConst (RoseTree a)) ix0
                f = from
                g :: IxTConst (RoseTree a) ix0 -> RoseTree a
                g = to
                conv :: IxTConst (RoseTree a) :-> IxProj (Right '()) (IxTConst a `IxTEither` IxTConst (RoseTree a))
                conv = f . g

toRose :: forall a ix. Rose (IxTConst a) ix -> RoseTree a
toRose = to . (algebra `ixcata`)
    where
        algebra :: forall ix. RoseFunctor (IxTConst a `IxTEither` IxTConst (RoseTree a)) ix -> IxTConst (RoseTree a) ix
        algebra xs = from $ RoseTree x (toList xs'')
            where
                z :: (a, List (IxProj (Right '()) (IxTConst a `IxTEither` IxTConst (RoseTree a))) ix)
                z@(x, xs') = to xs
                f :: RoseTree a -> IxTConst (RoseTree a) ix0
                f = from
                g :: IxProj (Right '()) (IxTConst a `IxTEither` IxTConst (RoseTree a)) ix0 -> RoseTree a
                g = to
                conv :: IxProj (Right '()) (IxTConst a `IxTEither` IxTConst (RoseTree a)) :-> IxTConst (RoseTree a)
                conv = f . g
                xs'' :: List (IxTConst (RoseTree a)) ix
                xs'' = conv `ixmap` xs'

instance Isomorphic a b => Isomorphic (RoseTree a) (Rose (IxTConst b) ix) where
    from = fromRose . (from `mapRose`)

    to = (to `mapRose`) . toRose

mapRose :: (a -> b) -> RoseTree a -> RoseTree b
mapRose f = toRose . (liftIxTConst f `ixmap`) . fromRose

--cataRose :: forall a b. ((a, [b]) -> b) -> RoseTree a -> b
--cataRose algebra = isoToLeft (alg `ixcata`)
--    where
--        alg :: RoseFunctor (IxTConst a `IxTEither` IxTConst b) :-> IxTConst b
--        alg = isoToRight algebra

x :: IxProj (Right '()) (IxTEither (IxTConst Bool) (IxTConst Integer)) ix
x = IxProj $ IxTEitherRight $ IxTConst 5

z :: Integer
z = to x

