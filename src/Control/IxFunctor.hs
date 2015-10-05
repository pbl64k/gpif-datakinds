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
Module      : Control.IxFunctor
Description : Free (co)recursion schemes for a broad range of algebraic data types
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

This module re-exports a bunch of stuff from other modules that should be
completely sufficient to define your own data types and get the recursion
schemes for them from the generic implementations.
-}

module Control.IxFunctor
        ( Void
        , Equality(Reflexivity)
        , Isomorphic(from, to)
        , isoToLeft
        , isoToRight
        , (:->)
        , IxTVoid
        , IxTConst(IxTConst)
        , liftIxTConst
        , IxTEither(IxTEitherLeft, IxTEitherRight)
        , split
        , IxTPair(IxTPair)
        , IxFunctor(ixmap)
        , IxVoid
        , IxUnit(IxUnit)
        , (:+:)(IxLeft, IxRight)
        , (:*:)(IxProd)
        , (:.:)(IxComp)
        , IxProj(IxProj)
        , IxOut(IxOut)
        , IxFix(IxFix)
        , ixunfix
        , ixcata
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
import Control.IxFunctor.RecScheme

