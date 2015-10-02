{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

{-|
Module      : Control.IxFunctor.Equality
Description : Propositional type equality
Copyright   : Pavel Lepin, 2015
License     : BSD2
Maintainer  : pbl64k@gmail.com
Stability   : experimental
Portability : GHC >= 7.8

Just to avoid depending on external libraries in a purely experimental project.
-}

module Control.IxFunctor.Equality
        ( Equality(Reflexivity)
        ) where

-- |Witnesses equality between types `a` and `b`.
-- Should only be constructible by invoking reflexivity of the equality relation.
data Equality a b where
    Reflexivity :: Equality a a

