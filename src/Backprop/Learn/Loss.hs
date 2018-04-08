{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Backprop.Learn.Loss (
    Loss
  , crossEntropy
  , squaredError, absError, totalSquaredError, squaredErrorV
  , scaleLoss
  , sumLoss
  , sumLossDecay
  , lastLoss
  , zipLoss
  , t2Loss
  , t3Loss
  ) where

import           Control.Applicative
import           Data.Finite
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import qualified Data.Vector.Sized                     as SV
import qualified Prelude.Backprop                      as B

type Loss a = forall s. Reifies s W => a -> BVar s a -> BVar s Double

crossEntropy :: KnownNat n => Loss (R n)
crossEntropy targ res = -(log res <.> constVar targ)

squaredErrorV :: KnownNat n => Loss (R n)
squaredErrorV targ res = norm_2V (res - constVar targ)

totalSquaredError :: (Num (t Double), Foldable t, Functor t) => Loss (t Double)
totalSquaredError targ res = B.sum (e * e)
  where
    e = constVar targ - res

squaredError :: Loss Double
squaredError targ res = (res - constVar targ) ** 2

absError :: Loss Double
absError targ res = abs (res - constVar targ)

-- klDivergence :: Loss Double
-- klDivergence = 

sumLoss
    :: (Traversable t, Applicative t, Num a)
    => Loss a
    -> Loss (t a)
sumLoss l targ = sum . liftA2 l targ . sequenceVar

zipLoss
    :: (Traversable t, Applicative t, Num a)
    => t Double
    -> Loss a
    -> Loss (t a)
zipLoss xs l targ = sum
                  . liftA3 (\α t -> (* constVar α) . l t) xs targ
                  . sequenceVar

sumLossDecay
    :: forall n a. (KnownNat n, Num a)
    => Double
    -> Loss a
    -> Loss (SV.Vector n a)
sumLossDecay β = zipLoss $ SV.generate (\i -> β ** (fromIntegral i - n))
  where
    n = fromIntegral $ maxBound @(Finite n)

lastLoss
    :: (KnownNat (n + 1), Num a)
    => Loss a
    -> Loss (SV.Vector (n + 1) a)
lastLoss l targ = l (SV.last targ) . viewVar (SV.ix maxBound)

-- | Scale the result of a loss function.
scaleLoss :: Double -> Loss a -> Loss a
scaleLoss β l x = (* constVar β) . l x

-- | Lift and sum a loss function over the components of a 'T2'.
t2Loss
    :: (Num a, Num b)
    => Loss a                   -- ^ loss on first component
    -> Loss b                   -- ^ loss on second component
    -> Loss (T2 a b)
t2Loss f g (T2 xT yT) xRyR = f xT (xRyR ^^. t2_1)
                           + g yT (xRyR ^^. t2_2)

-- | Lift and sum a loss function over the components of a 'T3'.
t3Loss
    :: (Num a, Num b, Num c)
    => Loss a                   -- ^ loss on first component
    -> Loss b                   -- ^ loss on second component
    -> Loss c                   -- ^ loss on third component
    -> Loss (T3 a b c)
t3Loss f g h (T3 xT yT zT) xRyRzR
        = f xT (xRyRzR ^^. t3_1)
        + g yT (xRyRzR ^^. t3_2)
        + h zT (xRyRzR ^^. t3_3)
