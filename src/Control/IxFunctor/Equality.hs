{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Control.IxFunctor.Equality
        ( Equality(Reflexivity)
        ) where

data Equality a b where
    Reflexivity :: Equality a a

