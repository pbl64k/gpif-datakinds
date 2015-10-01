{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.IxFunctor.ShowInstances where

import Control.IxFunctor.Equality
import Control.IxFunctor.IxType
import Control.IxFunctor.IxFunctor

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

