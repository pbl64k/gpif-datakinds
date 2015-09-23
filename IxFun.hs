{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE InstanceSigs #-}

data Void

type t :-> v = forall ix. t ix -> v ix

lift :: (t -> v) -> Const t :-> Const v
lift f (Const x) = Const $ f x

class IxFunctor (xf :: (inputIndex -> *) -> outputIndex -> *) where
    ixmap :: (t :-> v) -> xf t :-> xf v

data IxVoid :: (inputIndex -> *) -> outputIndex -> * where

instance IxFunctor IxVoid where
    ixmap _ _ = undefined

data IxUnit :: (inputIndex -> *) -> outputIndex -> * where
    IxUnit :: IxUnit r o

instance IxFunctor IxUnit where
    ixmap _ _ = IxUnit

data (:+:) ::
        ((inputIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxLeft :: (IxFunctor xf, IxFunctor xg) => xf r o -> (xf :+: xg) r o
    IxRight :: (IxFunctor xf, IxFunctor xg) => xg r o -> (xf :+: xg) r o

instance IxFunctor (xf :+: xg) where
    ixmap f (IxLeft xf) = IxLeft $ ixmap f xf
    ixmap f (IxRight xg) = IxRight $ ixmap f xg

data (:*:) ::
        ((inputIndex -> *) -> outputIndex -> *) ->
        ((inputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxProd :: (IxFunctor xf, IxFunctor xg) => xf r o -> xg r o -> (xf :*: xg) r o

instance IxFunctor (xf :*: xg) where
    ixmap f (IxProd xf xg) = IxProd (ixmap f xf) (ixmap f xg)

data Const :: * -> k -> * where
    Const :: t -> Const t k

data Case :: (t -> *) -> (v -> *) -> Either t v -> * where
    CaseLeft :: xf t -> Case xf xg (Left t)
    CaseRight :: xg v -> Case xf xg (Right v)

liftCase :: (t :-> v) -> (s :-> u) -> Case t s :-> Case v u
liftCase f _ (CaseLeft xf) = CaseLeft $ f xf
liftCase _ f (CaseRight xf) = CaseRight $ f xf

data IxProj :: inputIndex -> (inputIndex -> *) -> outputIndex -> * where
    IxProj :: r i -> IxProj i r o

instance IxFunctor (IxProj ix) where
    ixmap f (IxProj x) = IxProj $ f x

data IxFix ::
        ((Either inputIndex outputIndex -> *) -> outputIndex -> *) ->
        (inputIndex -> *) -> outputIndex -> * where
    IxIn :: (IxFunctor xf) => xf (Case r (IxFix xf r)) o -> IxFix xf r o

instance IxFunctor (IxFix xf) where
    ixmap :: forall t v. (t :-> v) -> IxFix xf t :-> IxFix xf v
    ixmap f (IxIn xf) = IxIn $ ixmap f' xf
        where
            f' :: Case t (IxFix xf t) :-> Case v (IxFix xf v)
            f' = liftCase f (ixmap f)

ixcata :: forall xf r s. IxFunctor xf => xf (Case r s) :-> s -> IxFix xf r :-> s
ixcata algebra (IxIn x) = algebra (ixmap f x)
    where
        f :: Case r (IxFix xf r) :-> Case r s
        f = liftCase id (ixcata algebra)

ixana :: forall xf r s. IxFunctor xf => s :-> xf (Case r s) -> s :-> IxFix xf r
ixana coalgebra x = IxIn $ ixmap f (coalgebra x)
    where
        f :: Case r s :-> Case r (IxFix xf r)
        f = liftCase id (ixana coalgebra)

unit :: IxUnit (Const Void) ()
unit = IxUnit

tst :: IxProj (Left ()) (Case (Const Int) (Const Void)) ()
tst = IxProj $ CaseLeft $ Const 1

type ListFunctor = IxUnit :+: (IxProj (Left ()) :*: IxProj (Right ()))

type List = IxFix ListFunctor

fromList :: [a] -> List (Const a) ()
fromList [] = IxIn $ IxLeft IxUnit
fromList (x : xs) = IxIn $ IxRight $ IxProd (IxProj $ CaseLeft $ Const x) (IxProj $ CaseRight $ fromList xs)

toList :: List (Const a) () -> [a]
toList (IxIn (IxLeft _)) = []
toList (IxIn (IxRight (IxProd (IxProj (CaseLeft (Const x))) (IxProj (CaseRight xs))))) = x : toList xs

foldList :: forall a b. a -> (a -> b -> a) -> [b] -> a
foldList nil cons = unpack . ixcata algebra . fromList
    where
        unpack (Const a) = a
        algebra :: ListFunctor (Case (Const b) (Const a)) :-> Const a
        algebra (IxLeft _) = Const nil
        algebra (IxRight (IxProd (IxProj (CaseLeft (Const x))) (IxProj (CaseRight (Const y))))) = Const $ cons y x

unfoldList :: forall a b. a -> (a -> Maybe (b, a)) -> [b]
unfoldList unnil uncons = toList $ ixana coalgebra (Const unnil)
    where
        coalgebra :: Const a :-> ListFunctor (Case (Const b) (Const a))
        coalgebra (Const x) = xform $ uncons x
            where
                xform Nothing = IxLeft IxUnit
                xform (Just (x, y)) = IxRight $ IxProd (IxProj $ CaseLeft $ Const x) (IxProj $ CaseRight $ Const y)

factorial n = foldList 1 (*) $ unfoldList n coalg
    where
        coalg 0 = Nothing
        coalg n = Just (n, pred n)

