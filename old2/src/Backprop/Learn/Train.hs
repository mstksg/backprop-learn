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
    gradLearnLoss
  , gradLearnStochLoss
  -- * Opto
  , Grad
  , learnGrad
  , learnGradStoch
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
gradLearnLoss
    :: ( Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Backprop (LParam l)
       )
    => Loss b
    -> Regularizer (LParam l)
    -> l
    -> LParam l
    -> a
    -> b
    -> LParam l
gradLearnLoss loss reg l p x y = gradBP (\p' ->
        loss y (runLearnStateless l (J_ p') (constVar x)) + reg p'
    ) p

-- | Stochastic gradient of model with respect to loss function and target
gradLearnStochLoss
    :: ( Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Backprop (LParam l)
       , PrimMonad m
       )
    => Loss b
    -> Regularizer (LParam l)
    -> l
    -> MWC.Gen (PrimState m)
    -> LParam l
    -> a
    -> b
    -> m (LParam l)
gradLearnStochLoss loss reg l g p x y = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ gradBP (\p' -> runST $ do
        g' <- MWC.initialize seed
        lo <- loss y <$> runLearnStochStateless l g' (J_ p') (constVar x)
        pure (lo + reg p')
      ) p

-- | Using a model's deterministic prediction function (with a given loss
-- function), generate a 'Grad' compatible with "Numeric.Opto" and
-- "Numeric.Opto.Run".
learnGrad
    :: ( MonadSample (a, b) m
       , Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Backprop (LParam l)
       )
    => Loss b
    -> Regularizer (LParam l)
    -> l
    -> Grad m (LParam l)
learnGrad loss reg l = pureSampling $ \(x,y) p -> gradLearnLoss loss reg l p x y

-- | Using a model's stochastic prediction function (with a given loss
-- function), generate a 'Grad' compatible with "Numeric.Opto" and
-- "Numeric.Opto.Run".
learnGradStoch
    :: ( MonadSample (a, b) m
       , PrimMonad m
       , Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Backprop (LParam l)
       )
    => Loss b
    -> Regularizer (LParam l)
    -> l
    -> MWC.Gen (PrimState m)
    -> Grad m (LParam l)
learnGradStoch loss reg l g = sampling $ \(x,y) p ->
      gradLearnStochLoss loss reg l g p x y
