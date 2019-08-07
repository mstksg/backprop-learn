{-# LANGUAGE DataKinds                     #-}
{-# LANGUAGE FlexibleContexts              #-}
{-# LANGUAGE RankNTypes                    #-}
{-# LANGUAGE ScopedTypeVariables           #-}
{-# LANGUAGE TypeApplications              #-}
{-# LANGUAGE TypeOperators                 #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Backprop.Learn.Loss (
  -- * Loss functions
    Loss
  , crossEntropy, crossEntropy1
  , squaredError, absError, totalSquaredError, squaredErrorV
  -- , totalCov
  -- ** Manipulate loss functions
  , scaleLoss
  , sumLoss
  , sumLossDecay
  , lastLoss
  , zipLoss
  , t2Loss
  -- * Regularization
  , Regularizer
  , l2Reg
  , l1Reg
  , noReg
  -- ** Manipulate regularizers
  , addReg
  , scaleReg
  ) where

import           Backprop.Learn.Regularize
import           Control.Applicative
import           Data.Coerce
import           Data.Finite
import           Data.Type.Tuple
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import qualified Data.Vector.Sized                     as SV
import qualified Prelude.Backprop                      as B

type Loss a = forall s. Reifies s W => a -> BVar s a -> BVar s Double

crossEntropy :: KnownNat n => Loss (R n)
crossEntropy targ res = -(log res <.> auto targ)

crossEntropy1 :: Loss Double
crossEntropy1 targ res = -(log res * auto targ + log (1 - res) * auto (1 - targ))

squaredErrorV :: KnownNat n => Loss (R n)
squaredErrorV targ res = e <.> e
  where
    e = res - auto targ

totalSquaredError
  :: (Backprop (t Double), Num (t Double), Foldable t, Functor t)
    => Loss (t Double)
totalSquaredError targ res = B.sum (e * e)
  where
    e = auto targ - res

squaredError :: Loss Double
squaredError targ res = (res - auto targ) ** 2

absError :: Loss Double
absError targ res = abs (res - auto targ)

-- -- | Sum of covariances between matching components.  Not sure if anyone
-- -- uses this.
-- totalCov :: (Backprop (t Double), Foldable t, Functor t) => Loss (t Double)
-- totalCov targ res = -(xy / fromIntegral n - (x * y) / fromIntegral (n * n))
--   where
--     x = auto $ sum targ
--     y = B.sum res
--     xy = B.sum (auto targ * res)
--     n = length targ

-- klDivergence :: Loss Double
-- klDivergence =

sumLoss
    :: (Traversable t, Applicative t, Backprop a)
    => Loss a
    -> Loss (t a)
sumLoss l targ = sum . liftA2 l targ . sequenceVar

zipLoss
    :: (Traversable t, Applicative t, Backprop a)
    => t Double
    -> Loss a
    -> Loss (t a)
zipLoss xs l targ = sum
                  . liftA3 (\α t -> (* auto α) . l t) xs targ
                  . sequenceVar

sumLossDecay
    :: forall n a. (KnownNat n, Backprop a)
    => Double
    -> Loss a
    -> Loss (SV.Vector n a)
sumLossDecay β = zipLoss $ SV.generate (\i -> β ** (fromIntegral i - n))
  where
    n = fromIntegral $ maxBound @(Finite n)

lastLoss
    :: forall n a. (KnownNat (n + 1), Backprop a)
    => Loss a
    -> Loss (SV.Vector (n + 1) a)
lastLoss l targ = l (SV.last targ)
                . viewVar (coerced . SV.ix @(n + 1) maxBound)
                . B.coerce @_ @(ABP (SV.Vector (n + 1)) a)

coerced :: Coercible a b => Lens' a b
coerced f x = coerce <$> f (coerce x)
{-# INLINE coerced #-}

-- | Scale the result of a loss function.
scaleLoss :: Double -> Loss a -> Loss a
scaleLoss β l x = (* auto β) . l x

-- | Lift and sum a loss function over the components of a ':&'.
t2Loss
    :: (Backprop a, Backprop b)
    => Loss a                   -- ^ loss on first component
    -> Loss b                   -- ^ loss on second component
    -> Loss (a :# b)
t2Loss f g (xT :# yT) (xR :## yR) = f xT xR + g yT yR

