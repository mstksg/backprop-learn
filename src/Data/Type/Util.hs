{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Type.Util (
    replWit
  , replLen
  , prodToVec'
  , vecToProd
  , vtraverse
  , zipP
  ) where

import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Nat
import           Data.Type.Product
import           Data.Type.Vector
import           Numeric.Backprop.Op (Replicate)
import           Type.Class.Witness


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
