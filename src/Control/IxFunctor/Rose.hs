{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module Control.IxFunctor.Rose
        ( RoseFunctor
        , Rose
        , fromRose
        , toRose
        --, mapRose
        --, cataRose
        --, anaRose
        --, hyloRose
        --, paraRose
        ) where

import Control.IxFunctor.RecScheme
import Control.IxFunctor.List

data RoseTree a = RoseTree a [RoseTree a]

type RoseFunctor = ((IxProj (Left '()) :*: (List :.: IxProj (Right '()))) :: (Either () () -> *) -> () -> *)

type Rose = IxFix RoseFunctor

fromRose :: forall a ix. RoseTree a -> Rose (IxTConst a) ix
fromRose = (coalgebra `ixana`) . from
    where
        coalgebra :: forall ix. IxTConst (RoseTree a) ix -> RoseFunctor (IxTConst a `IxTEither` IxTConst (RoseTree a)) ix
        coalgebra (IxTConst (RoseTree x xs)) = from (x, conv `ixmap` xs')
            where
                xs' :: List (IxTConst (RoseTree a)) ix
                xs' = from xs
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
        algebra xs = from $ RoseTree x (to xs'')
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

