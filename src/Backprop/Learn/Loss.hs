{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Backprop.Learn.Loss (
    LossFunction
  , crossEntropy
  , squaredError, squaredError1
  , sumLoss
  , sumLossDecay
  , lastLoss
  , zipLoss
  ) where

import           Control.Applicative
import           Data.Finite
import           Data.Proxy
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import qualified Data.Vector.Sized                     as SV
import qualified Prelude.Backprop                      as B

type LossFunction a = forall s. Reifies s W => a -> BVar s a -> BVar s Double

crossEntropy :: KnownNat n => LossFunction (R n)
crossEntropy targ res = -(log res <.> constVar targ)

squaredError :: KnownNat n => LossFunction (R n)
squaredError targ res = norm_2V (res - constVar targ)

squaredError1 :: LossFunction Double
squaredError1 targ res = (res - constVar targ) ** 2

sumLoss
    :: (Traversable t, Applicative t, Num a)
    => LossFunction a
    -> LossFunction (t a)
sumLoss l targ = sum . liftA2 l targ . sequenceVar

zipLoss
    :: (Traversable t, Applicative t, Num a)
    => t Double
    -> LossFunction a
    -> LossFunction (t a)
zipLoss xs l targ = sum
                  . liftA3 (\α t -> (* constVar α) . l t) xs targ
                  . sequenceVar

sumLossDecay
    :: forall n a. (KnownNat n, Num a)
    => Double
    -> LossFunction a
    -> LossFunction (SV.Vector n a)
sumLossDecay β = zipLoss $ SV.generate (\i -> β ** (fromIntegral i - n))
  where
    n = fromIntegral $ maxBound @(Finite n)

lastLoss
    :: (KnownNat (n + 1), Num a)
    => LossFunction a
    -> LossFunction (SV.Vector (n + 1) a)
lastLoss l targ = l (SV.last targ) . viewVar (SV.ix maxBound)
