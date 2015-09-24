{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}

type t :-> v = forall ix. t ix -> v ix

data Const :: * -> k -> * where
    Const :: t -> Const t k

unconst :: Const t k -> t
unconst (Const x) = x

data Union :: (t -> *) -> (v -> *) -> Either t v -> * where
    UnionLeft :: xf t -> Union xf xg (Left t)
    UnionRight :: xg v -> Union xf xg (Right v)

split :: (t :-> v) -> (s :-> u) -> Union t s :-> Union v u
split f _ (UnionLeft xf) = UnionLeft $ f xf
split _ f (UnionRight xf) = UnionRight $ f xf

lift :: (t -> v) -> Const t :-> Const v
lift f (Const x) = Const $ f x

class IxFunctor (xf :: (inputIndex -> *) -> outputIndex -> *) where
    ixmap :: (t :-> v) -> xf t :-> xf v

data IxVoid :: (inputIndex -> *) -> outputIndex -> *

instance IxFunctor IxVoid where
    _ `ixmap` _ = undefined

data IxUnit :: (inputIndex -> *) -> outputIndex -> * where
    IxUnit :: IxUnit r o

instance IxFunctor IxUnit where
    _ `ixmap` _ = IxUnit

data (:+:) ::
        ((inputIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxLeft :: (IxFunctor xf, IxFunctor xg) => xf r o -> (xf :+: xg) r o
    IxRight :: (IxFunctor xf, IxFunctor xg) => xg r o -> (xf :+: xg) r o

instance IxFunctor (xf :+: xg) where
    f `ixmap` (IxLeft xf) = IxLeft $ f `ixmap` xf
    f `ixmap` (IxRight xg) = IxRight $ f `ixmap` xg

data (:*:) ::
        ((inputIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxProd :: (IxFunctor xf, IxFunctor xg) => xf r o -> xg r o -> (xf :*: xg) r o

instance IxFunctor (xf :*: xg) where
    f `ixmap` (xf `IxProd` xg) = (f `ixmap` xf) `IxProd` (f `ixmap` xg)

data IxProj :: inputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxProj :: r i -> IxProj i r o

instance IxFunctor (IxProj ix) where
    ixmap f (IxProj x) = IxProj $ f x

data IxFix ::
        ((Either inputIndex outputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxIn :: IxFunctor xf => xf (Union r (IxFix xf r)) o -> IxFix xf r o

instance IxFunctor (IxFix xf) where
    ixmap :: forall t v. (t :-> v) -> IxFix xf t :-> IxFix xf v
    f `ixmap` (IxIn xf) = IxIn $ f' `ixmap` xf
        where
            f' :: Union t (IxFix xf t) :-> Union v (IxFix xf v)
            f' = f `split` (f `ixmap`)

ixcata :: forall xf r s. IxFunctor xf => xf (Union r s) :-> s -> IxFix xf r :-> s
algebra `ixcata` (IxIn x) = algebra (f `ixmap` x)
    where
        f :: Union r (IxFix xf r) :-> Union r s
        f = id `split` (algebra `ixcata`)

ixana :: forall xf r s. IxFunctor xf => s :-> xf (Union r s) -> s :-> IxFix xf r
coalgebra `ixana` x = IxIn $ f `ixmap` (coalgebra x)
    where
        f :: Union r s :-> Union r (IxFix xf r)
        f = id `split` (coalgebra `ixana`)

type ListFunctor = IxUnit :+: (IxProj (Left ()) :*: IxProj (Right ()))

type List = IxFix ListFunctor

fromList :: [a] -> List (Const a) ()
fromList [] = IxIn $ IxLeft IxUnit
fromList (x : xs) = IxIn $ IxRight $ (IxProj $ UnionLeft $ Const x) `IxProd` (IxProj $ UnionRight $ fromList xs)

toList :: List (Const a) () -> [a]
toList (IxIn (IxLeft _)) = []
toList (IxIn (IxRight ((IxProj (UnionLeft (Const x))) `IxProd` (IxProj (UnionRight xs))))) = x : toList xs

foldList :: forall a b. a -> (a -> b -> a) -> [b] -> a
foldList nil cons = unconst . (algebra `ixcata`) . fromList
    where
        algebra :: ListFunctor (Union (Const b) (Const a)) :-> Const a
        algebra (IxLeft _) = Const nil
        algebra (IxRight ((IxProj (UnionLeft (Const x))) `IxProd` (IxProj (UnionRight (Const y))))) = Const $ cons y x

unfoldList :: forall a b. a -> (a -> Maybe (b, a)) -> [b]
unfoldList unnil uncons = toList $ coalgebra `ixana` Const unnil
    where
        coalgebra :: Const a :-> ListFunctor (Union (Const b) (Const a))
        coalgebra (Const x) = xform $ uncons x
            where
                xform Nothing = IxLeft IxUnit
                xform (Just (x, y)) = IxRight $ (IxProj $ UnionLeft $ Const x) `IxProd` (IxProj $ UnionRight $ Const y)

factorial n = foldList 1 (*) $ unfoldList n coalg
    where
        coalg 0 = Nothing
        coalg n = Just (n, pred n)

