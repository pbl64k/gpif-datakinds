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

module Control.IxFunctor.RecScheme
        ( ixcata
        , ixana
        , ixhylo
        , ixmeta
        , ixpara
        , ixapo
        ) where

import Control.IxFunctor.Equality
import Control.IxFunctor.Iso
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor

ixcata :: forall xf r s. IxFunctor xf => xf (r `IxTEither` s) :-> s -> IxFix xf r :-> s
ixcata algebra = algebra . (f `ixmap`) . ixunfix
    where
        f :: IxTEither r (IxFix xf r) :-> IxTEither r s
        f = id `split` (algebra `ixcata`)

ixana :: forall xf r s. IxFunctor xf => s :-> xf (r `IxTEither` s) -> s :-> IxFix xf r
ixana coalgebra = IxFix . (f `ixmap`) . coalgebra
    where
        f :: IxTEither r s :-> IxTEither r (IxFix xf r)
        f = id `split` (coalgebra `ixana`)

ixhylo :: forall xf r s t. IxFunctor xf =>
        xf (r `IxTEither` t) :-> t -> s :-> xf (r `IxTEither` s) -> s :-> t
ixhylo algebra coalgebra = algebra . (f `ixmap`) . coalgebra
    where
        f :: IxTEither r s :-> IxTEither r t
        f = id `split` (ixhylo algebra coalgebra)

ixmeta :: forall xf xg r s t. (IxFunctor xf, IxFunctor xg) =>
        s :-> xg (t `IxTEither` s) -> xf (r `IxTEither` s) :-> s -> IxFix xf r :-> IxFix xg t
ixmeta coalgebra algebra = (coalgebra `ixana`) . (algebra `ixcata`)

ixpara :: forall xf r s. IxFunctor xf =>
        xf (r `IxTEither` (s `IxTPair` IxFix xf r)) :-> s -> IxFix xf r :-> s
ixpara algebra = algebra . (f `ixmap`) . ixunfix
    where
        f :: IxTEither r (IxFix xf r) :-> IxTEither r (s `IxTPair` IxFix xf r)
        f = id `split` ((algebra `ixpara`) `fanout` id)
            where
                fanout f g x = f x `IxTPair` g x

ixapo :: forall xf r s. IxFunctor xf =>
        s :-> xf (r `IxTEither` (s `IxTChoice` IxFix xf r)) -> s :-> IxFix xf r
ixapo coalgebra = IxFix . (f `ixmap`) . coalgebra
    where
        f :: IxTEither r (s `IxTChoice` IxFix xf r) :-> IxTEither r (IxFix xf r)
        f = id `split` ((coalgebra `ixapo`) `choice` id)
            where
                choice f _ (IxTChoiceLeft x) = f x
                choice _ f (IxTChoiceRight x) = f x

