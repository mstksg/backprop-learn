{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Backprop.Learn.Loss (
  -- * Loss functions
    Loss
  , crossEntropy
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

import           Control.Applicative
import           Data.Coerce
import           Data.Finite
import           Data.Type.Tuple
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.Opto.Update hiding            ((<.>))
import qualified Data.Vector.Sized                     as SV
import qualified Prelude.Backprop                      as B

type Loss a = forall s. Reifies s W => a -> BVar s a -> BVar s Double

crossEntropy :: KnownNat n => Loss (R n)
crossEntropy targ res = -(log res <.> constVar targ)

squaredErrorV :: KnownNat n => Loss (R n)
squaredErrorV targ res = e <.> e
  where
    e = res - constVar targ

totalSquaredError
  :: (Backprop (t Double), Num (t Double), Foldable t, Functor t)
    => Loss (t Double)
totalSquaredError targ res = B.sum (e * e)
  where
    e = constVar targ - res

squaredError :: Loss Double
squaredError targ res = (res - constVar targ) ** 2

absError :: Loss Double
absError targ res = abs (res - constVar targ)

-- -- | Sum of covariances between matching components.  Not sure if anyone
-- -- uses this.
-- totalCov :: (Backprop (t Double), Foldable t, Functor t) => Loss (t Double)
-- totalCov targ res = -(xy / fromIntegral n - (x * y) / fromIntegral (n * n))
--   where
--     x = constVar $ sum targ
--     y = B.sum res
--     xy = B.sum (constVar targ * res)
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
                  . liftA3 (\α t -> (* constVar α) . l t) xs targ
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
scaleLoss β l x = (* constVar β) . l x

-- | Lift and sum a loss function over the components of a ':&'.
t2Loss
    :: (Backprop a, Backprop b)
    => Loss a                   -- ^ loss on first component
    -> Loss b                   -- ^ loss on second component
    -> Loss (a :& b)
t2Loss f g (xT :& yT) (xR :&& yR) = f xT xR + g yT yR

-- | A regularizer on parameters
type Regularizer p = forall s. Reifies s W => BVar s p -> BVar s Double

-- | L2 regularization
--
-- \[
-- \sum_w \frac{1}{2} w^2
-- \]
l2Reg
    :: (Metric Double p, Backprop p)
    => Double                   -- ^ scaling factor (often 0.5)
    -> Regularizer p
l2Reg λ = liftOp1 . op1 $ \x ->
            ( λ * quadrance x / 2, (.* x) . (* λ))

-- | L1 regularization
--
-- \[
-- \sum_w \lvert w \rvert
-- \]
l1Reg
    :: (Num p, Metric Double p, Backprop p)
    => Double                   -- ^ scaling factor (often 0.5)
    -> Regularizer p
l1Reg λ = liftOp1 . op1 $ \x ->
            ( λ * norm_1 x, (.* signum x) . (* λ)
            )

-- | No regularization
noReg :: Regularizer p
noReg _ = constVar 0

-- | Add together two regularizers
addReg :: Regularizer p -> Regularizer p -> Regularizer p
addReg = liftA2 (+)

-- | Scale a regularizer's influence
scaleReg :: Double -> Regularizer p -> Regularizer p
scaleReg λ reg = (* constVar λ) . reg
