{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}

module Backprop.Learn.Regularize (
    Regularizer
  , Regularize(..)
  , noReg
  , l2RegDefault
  , l1RegDefault
  -- ** Manipulate regularizers
  , addReg
  , scaleReg
  ) where

import           Numeric.Backprop
import           Generics.OneLiner
import           Numeric.Opto.Update hiding ((<.>))
import           Data.Semigroup

-- | A regularizer on parameters
type Regularizer p = forall s. Reifies s W => BVar s p -> BVar s Double

class Backprop p => Regularize p where
    -- | L1 regularization
    --
    -- \[
    -- \sum_w \lvert w \rvert
    -- \]
    --
    -- Note that typically bias terms (terms that add to inputs) are not
    -- regularized.  Only "weight" terms that scale inputs are typically
    -- regularized.
    l1Reg :: Double -> Regularizer p

    default l1Reg :: (ADT p, Constraints p Regularize) => Double -> Regularizer p
    l1Reg λ = undefined
    -- l1Reg λ = liftOp1 . op1 $ \x ->
    --     ( getSum . gfoldMap @Regularize (\y -> Sum $ evalBP (l1Reg λ) y) $ x
    --     , \g -> 
    --     )
    -- getSum . gfoldMap @Regularize (Sum . l1Reg)

    -- | L2 regularization
    --
    -- \[
    -- \sum_w \frac{1}{2} w^2
    -- \]
    --
    -- Note that typically bias terms (terms that add to inputs) are not
    -- regularized.  Only "weight" terms that scale inputs are typically
    -- regularized.
    l2Reg :: Double -> Regularizer p

-- | No regularization
noReg :: Regularizer p
noReg _ = auto 0

-- | Defalt L2 regularization for instances of 'Metric'.  This will count
-- all terms, including any potential bias terms.
l2RegDefault
    :: (Metric Double p, Backprop p)
    => Double                   -- ^ scaling factor (often 0.5)
    -> Regularizer p
l2RegDefault λ = liftOp1 . op1 $ \x ->
            ( λ * quadrance x / 2, (.* x) . (* λ))

-- | Defalt L1 regularization for instances of 'Metric'.  This will count
-- all terms, including any potential bias terms.
l1RegDefault
    :: (Num p, Metric Double p, Backprop p)
    => Double                   -- ^ scaling factor (often 0.5)
    -> Regularizer p
l1RegDefault λ = liftOp1 . op1 $ \x ->
            ( λ * norm_1 x, (.* signum x) . (* λ)
            )

-- | Add together two regularizers
addReg :: Regularizer p -> Regularizer p -> Regularizer p
addReg f g x = f x + g x

-- | Scale a regularizer's influence
scaleReg :: Double -> Regularizer p -> Regularizer p
scaleReg λ reg = (* auto λ) . reg
