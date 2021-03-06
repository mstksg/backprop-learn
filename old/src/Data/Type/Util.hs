{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# OPTIONS_GHC -fno-warn-orphans   #-}

module Data.Type.Util (
    MaybeToList
  , replWit
  , replLen
  , prodToVec'
  , vecToProd
  , vtraverse
  , vecLenNat
  , zipP
  , last'
  , takeVec
  , unzipVec
  ) where

import           Data.Finite
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product hiding (last')
import           Data.Type.Vector
import           Numeric.Backprop.Op      (Replicate)
import           Type.Class.Higher
import           Type.Class.Witness
import           Type.Family.Nat

type family MaybeToList (a :: Maybe k) = (b :: [k]) | b -> a where
    MaybeToList ('Just a ) = '[a]
    MaybeToList 'Nothing   = '[]

replWit
    :: forall n c a. ()
    => Nat n
    -> Wit (c a)
    -> Wit (Every c (Replicate n a))
replWit = \case
    Z_   -> (Wit \\)
    S_ n -> \case
      w@Wit -> Wit \\ replWit n w

replLen
    :: forall n a. ()
    => Nat n
    -> Length (Replicate n a)
replLen = \case
    Z_   -> LZ
    S_ n -> LS (replLen @_ @a n)

prodToVec'
    :: Nat n
    -> Prod f (Replicate n a)
    -> VecT n f a
prodToVec' = \case
    Z_   -> \case
      Ø -> ØV
    S_ n -> \case
      x :< xs ->
        x :* prodToVec' n xs

vecToProd
    :: VecT n f a
    -> Prod f (Replicate n a)
vecToProd = \case
    ØV      -> Ø
    x :* xs -> x :< vecToProd xs

vtraverse
    :: Applicative h
    => (f a -> h (g b))
    -> VecT n f a
    -> h (VecT n g b)
vtraverse f = \case
    ØV      -> pure ØV
    x :* xs -> (:*) <$> f x <*> vtraverse f xs

zipP
    :: Prod f as
    -> Prod g as
    -> Prod (f :&: g) as
zipP = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y:< ys -> (x :&: y) :< zipP xs ys

vecLenNat
    :: VecT n f a
    -> Nat n
vecLenNat = \case
    ØV      -> Z_
    _ :* xs -> S_ (vecLenNat xs)

instance Eq1 Finite

last'
    :: VecT ('S n) f a
    -> f a
last' = \case
    x :* ØV          -> x
    _ :* xs@(_ :* _) -> last' xs

takeVec
    :: Nat n
    -> [a]
    -> Maybe (Vec n a)
takeVec = \case
    Z_   -> \_ -> Just ØV
    S_ n -> \case
      []   -> Nothing
      x:xs -> (x :+) <$> takeVec n xs

unzipVec
    :: Vec n (a, b)
    -> (Vec n a, Vec n b)
unzipVec = \case
    ØV              -> (ØV, ØV)
    I (x,y) :* xsys ->
      let (xs, ys) = unzipVec xsys
      in  (I x :* xs, I y :* ys)
