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
  -- * Utility conduits
  , consecutives
  , consecutivesN
  ) where

import           Backprop.Learn.Loss
import           Backprop.Learn.Model
import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Control.Monad.Sample
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Data.Conduit
import           Data.Foldable
import           Data.Proxy
import           Data.Word
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Opto.Core
import qualified Data.Sequence             as Seq
import qualified Data.Vector.Generic       as VG
import qualified Data.Vector.Generic.Sized as SVG
import qualified Data.Vector.Unboxed       as VU
import qualified System.Random.MWC         as MWC

-- | Gradient of model with respect to loss function and target
gradLearnLoss
    :: ( Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Num (LParam l)
       )
    => Loss b
    -> l
    -> LParam l
    -> a
    -> b
    -> LParam l
gradLearnLoss loss l p x y = gradBP (\p' ->
        loss y (runLearnStateless l (J_ p') (constVar x))
    ) p

-- | Stochastic gradient of model with respect to loss function and target
gradLearnStochLoss
    :: ( Learn a b l
       , NoState l
       , LParamMaybe l ~ 'Just (LParam l)
       , Num (LParam l)
       , PrimMonad m
       )
    => Loss b
    -> l
    -> MWC.Gen (PrimState m)
    -> LParam l
    -> a
    -> b
    -> m (LParam l)
gradLearnStochLoss loss l g p x y = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ gradBP (\p' -> runST $ do
        g' <- MWC.initialize seed
        loss y <$> runLearnStochStateless l g' (J_ p') (constVar x)
      ) p

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
learnGrad loss l = pureSampling $ \(x,y) p -> gradLearnLoss loss l p x y

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
learnGradStoch loss l g = sampling $ \(x,y) p ->
      gradLearnStochLoss loss l g p x y

consecutives :: Monad m => ConduitT i (i, i) m ()
consecutives = void . runMaybeT $ do
    x <- MaybeT await
    go x
  where
    go x = do
      y <- MaybeT await
      lift $ yield (x, y)
      go y

consecutivesN
    :: forall v n i m. (KnownNat n, VG.Vector v i, Monad m)
    => ConduitT i (SVG.Vector v n i, SVG.Vector v n i) m ()
consecutivesN = void . runMaybeT $ do
    xs <- Seq.replicateM (fromIntegral n) $ MaybeT await
    go xs
  where
    go xs = do
      _ Seq.:<| xs' <- pure xs
      y <- MaybeT await
      let ys = xs' Seq.:|> y
      xsV <- MaybeT . pure . SVG.fromList . toList $ xs     -- should not fail
      ysV <- MaybeT . pure . SVG.fromList . toList $ ys     -- should not fail
      lift $ yield (xsV, ysV)
      go ys
    n = natVal (Proxy @n)
