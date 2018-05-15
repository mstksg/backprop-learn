{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Backprop.Learn.Model.Stochastic (
    dropout
  , rreLU
  , injectNoise, applyNoise
  , injectNoiseR, applyNoiseR
  ) where

import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Types
import           Control.Monad.Primitive
import           Data.Bool
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Statistics.Distribution               as Stat
import qualified System.Random.MWC                     as MWC
import qualified System.Random.MWC.Distributions       as MWC

-- | Dropout layer.  Parameterized by dropout percentage (should be between
-- 0 and 1).
--
-- 0 corresponds to no dropout, 1 corresponds to complete dropout of all
-- nodes every time.
dropout
    :: KnownNat n
    => Double
    -> Model 'Nothing 'Nothing (R n) (R n)
dropout r = Func
    { runFunc      = (auto (realToFrac (1 - r)) *)
    , runFuncStoch = \g x -> do
        (x *) . auto . vecR <$> SVS.replicateM (mask g)
    }
  where
    mask :: PrimMonad m => MWC.Gen (PrimState m) -> m Double
    mask = fmap (bool 1 0) . MWC.bernoulli r

-- | Random leaky rectified linear unit
rreLU
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> Model 'Nothing 'Nothing (R n) (R n)
rreLU d = Func
    { runFunc      = vmap' (preLU v)
    , runFuncStoch = \g x -> do
        α <- vecR <$> SVS.replicateM (Stat.genContVar d g)
        pure (zipWithVector preLU (constVar α) x)
    }
  where
    v :: BVar s Double
    v = auto (Stat.mean d)

-- | Inject random noise.  Usually used between neural network layers, or
-- at the very beginning to pre-process input.
--
-- In non-stochastic mode, this adds the mean of the distribution.
injectNoise
    :: (Stat.ContGen d, Stat.Mean d, Fractional a)
    => d
    -> Model 'Nothing 'Nothing a a
injectNoise d = Func
    { runFunc = (realToFrac (Stat.mean d) +)
    , runFuncStoch = \g x -> do
        e <- Stat.genContVar d g
        pure (realToFrac e + x)
    }

-- | 'injectNoise' lifted to 'R'
injectNoiseR
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> Model 'Nothing 'Nothing (R n) (R n)
injectNoiseR d = Func
    { runFunc = (realToFrac (Stat.mean d) +)
    , runFuncStoch  = \g x -> do
        e <- vecR <$> SVS.replicateM (Stat.genContVar d g)
        pure (constVar e + x)
    }

-- | Multply by random noise.  Can be used to implement dropout-like
-- behavior.
--
-- In non-stochastic mode, this scales by the mean of the distribution.
applyNoise
    :: (Stat.ContGen d, Stat.Mean d, Fractional a)
    => d
    -> Model 'Nothing 'Nothing a a
applyNoise d = Func
    { runFunc = (realToFrac (Stat.mean d) *)
    , runFuncStoch  = \g x -> do
        e <- Stat.genContVar d g
        pure (realToFrac e * x)
    }

-- | 'applyNoise' lifted to 'R'
applyNoiseR
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> Model 'Nothing 'Nothing (R n) (R n)
applyNoiseR d = Func
    { runFunc = (realToFrac (Stat.mean d) *)
    , runFuncStoch  = \g x -> do
        e <- vecR <$> SVS.replicateM (Stat.genContVar d g)
        pure (constVar e * x)
    }
