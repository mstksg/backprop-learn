{-# LANGUAGE DataKinds                            #-}
{-# LANGUAGE FlexibleContexts                     #-}
{-# LANGUAGE MultiParamTypeClasses                #-}
{-# LANGUAGE PartialTypeSignatures                #-}
{-# LANGUAGE RankNTypes                           #-}
{-# LANGUAGE TypeFamilies                         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Backprop.Learn.Train (
    Grad
  , learnGrad
  , learnGradStoch
  ) where

import           Backprop.Learn.Loss
import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Numeric.Backprop
import           Numeric.Opto.Core
import qualified System.Random.MWC       as MWC

-- | Using a model's deterministic prediction function (with a given loss
-- function), generate a 'Grad' compatible with "Numeric.Opto" and
-- "Numeric.Opto.Run".
learnGrad
    :: ( MonadSample (a, b) m
       , Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Num (LParam l)
       )
    => Loss b
    -> l
    -> Grad m (LParam l)
learnGrad loss l = pureSampling $ \(x,y) -> gradBP $ \p ->
      loss y (runLearnStateless l (J_ p) (constVar x))

-- | Using a model's stochastic prediction function (with a given loss
-- function), generate a 'Grad' compatible with "Numeric.Opto" and
-- "Numeric.Opto.Run".
learnGradStoch
    :: ( MonadSample (a, b) m
       , PrimMonad m
       , Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Num (LParam l)
       )
    => Loss b
    -> l
    -> MWC.Gen (PrimState m)
    -> Grad m (LParam l)
learnGradStoch loss l g = sampling $ \(x,y) p -> do
    g_ <- MWC.save g
        -- is there a better way to do this?
    let gradFunc :: forall s. Reifies s W => BVar s _ -> BVar s Double
        gradFunc p' = runST $ do
          g' <- MWC.restore g_
          r  <- runLearnStochStateless l g' (J_ p') (constVar x)
          pure $ loss y r
    pure (gradBP gradFunc p)
