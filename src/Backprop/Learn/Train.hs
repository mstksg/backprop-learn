{-# LANGUAGE DataKinds                            #-}
{-# LANGUAGE FlexibleContexts                     #-}
{-# LANGUAGE MultiParamTypeClasses                #-}
{-# LANGUAGE PartialTypeSignatures                #-}
{-# LANGUAGE RankNTypes                           #-}
{-# LANGUAGE ScopedTypeVariables                  #-}
{-# LANGUAGE TypeApplications                     #-}
{-# LANGUAGE TypeFamilies                         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Backprop.Learn.Train (
  -- * Gradients
    gradModelLoss
  , gradModelStochLoss
  -- * Opto
  , Grad
  , modelGrad
  , modelGradStoch
  ) where

import           Backprop.Learn.Loss
import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Control.Monad.Sample
import           Data.Word
import           Numeric.Backprop
import           Numeric.Opto.Core
import qualified Data.Vector.Unboxed          as VU
import qualified System.Random.MWC            as MWC

-- | Gradient of model with respect to loss function and target
gradModelLoss
    :: Backprop p
    => Loss b
    -> Regularizer p
    -> Model ('Just p) 'Nothing a b
    -> p
    -> a
    -> b
    -> p
gradModelLoss loss reg f p x y = gradBP (\p' ->
        loss y (runLearnStateless f (J_ p') (constVar x)) + reg p'
    ) p

-- | Stochastic gradient of model with respect to loss function and target
gradModelStochLoss
    :: (Backprop p, PrimMonad m)
    => Loss b
    -> Regularizer p
    -> Model ('Just p) 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> p
    -> a
    -> b
    -> m p
gradModelStochLoss loss reg f g p x y = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ gradBP (\p' -> runST $ do
        g' <- MWC.initialize seed
        lo <- loss y <$> runLearnStochStateless f g' (J_ p') (constVar x)
        pure (lo + reg p')
      ) p

-- | Using a model's deterministic prediction function (with a given loss
-- function), generate a 'Grad' compatible with "Numeric.Opto" and
-- "Numeric.Opto.Run".
modelGrad
    :: (MonadSample (a, b) m, Backprop p)
    => Loss b
    -> Regularizer p
    -> Model ('Just p) 'Nothing a b
    -> Grad m p
modelGrad loss reg f = pureSampling $ \(x,y) p -> gradModelLoss loss reg f p x y

-- | Using a model's stochastic prediction function (with a given loss
-- function), generate a 'Grad' compatible with "Numeric.Opto" and
-- "Numeric.Opto.Run".
modelGradStoch
    :: (MonadSample (a, b) m, PrimMonad m, Backprop p)
    => Loss b
    -> Regularizer p
    -> Model ('Just p) 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> Grad m p
modelGradStoch loss reg f g = sampling $ \(x,y) p ->
      gradModelStochLoss loss reg f g p x y
