{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Numeric.BLAS.Accelerate (
  ) where

import           Data.Finite
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           Data.Type.Product
import           Numeric.Tensor
import           Type.Class.Witness
import qualified Data.Array.Accelerate    as A

type family NatShape (as :: [Nat]) where
    NatShape '[]       = A.DIM0
    NatShape (a ': as) = NatShape as A.:. Int

sNatShape :: Sing as -> NatShape as
sNatShape = \case
    SNil         -> A.Z
    s `SCons` ss -> sNatShape ss A.:. fromIntegral (fromSing s)

shapeIndex
    :: Sing as -> NatShape as -> Prod Finite as
shapeIndex = \case
    SNil            -> \_ -> Ø
    SNat `SCons` ss -> \case
      is A.:. i -> fromIntegral i :< shapeIndex ss is

shapeWit :: forall s. Sing s -> Wit (A.Shape (NatShape s))
shapeWit = \case
    SNil         -> Wit
    _ `SCons` ss -> Wit \\ shapeWit ss

newtype AC :: [Nat] -> Type where
    AC :: A.Acc (A.Array (NatShape s) Double) -> AC s

newtype ACS :: Type where
    ACS :: A.Exp Double -> ACS
  deriving (Num, Fractional, Floating, Real, RealFrac, RealFloat, Eq, Ord)

instance Tensor AC where
    type Scalar AC = ACS

    gen s f = case shapeWit s of
      Wit -> AC . A.use $ A.fromFunction (sNatShape s) (realToFrac . f . shapeIndex s)

    genA s f = case shapeWit s of
      Wit -> AC . A.use . A.fromList (sNatShape s) <$> traverse (fmap realToFrac . f) (range s)

    -- tsum :: forall s. SingI s => AC s -> ACS
    -- tsum (AC a) = case shapeWit @s sing of
    --   Wit -> ACS . A.unlift $ A.sum a

