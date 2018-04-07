{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE DeriveDataTypeable                       #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Neural (
  -- * Fully connected
  -- ** Feed-forward
    FC, fc, FCp, fcBias, fcWeights
  -- *** With activation function
  , FCA, pattern FCA, fca, _fcaGen, _fcaActivation
  -- ** Recurrent
  , FCR, pattern FCR, fcr, FCRp, fcrBias, fcrInputWeights, fcrStateWeights
  -- *** With activation function
  , FCRA, pattern FCRA, fcra, _fcraGen, _fcraGenState, _fcraStore, _fcraActivation
  ) where


import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Regression
import           Backprop.Learn.Model.State
import           Control.Monad.Primitive
import           Data.Tuple
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Statistics.Distribution
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC


-- | Fully connected feed-forward layer with bias.  Parameterized by its
-- initialization distribution.
--
-- Note that this has no activation function; to use as a model with
-- activation function, chain it with an activation function using 'RMap',
-- ':.~', etc.; see 'FCA' for a convenient type synonym and constructor.
--
-- Without any activation function, this is essentially a multivariate
-- linear regression.
--
-- With the logistic function as an activation function, this is
-- essentially multivariate logistic regression. (See 'Logistic')
type FC i o = LinReg i o

pattern FC
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> FC i o
pattern FC { _fcGen } = LinReg _fcGen

-- | Construct an @'FC' i o@ using a given distribution from the
-- /statistics/ library.
fc :: ContGen d => d -> FC i o
fc = linReg

-- | Convenient synonym for an 'FC' post-composed with a simple
-- parameterless activation function.
type FCA i o = RMap (R o) (R o) (FC i o)

-- | Construct an 'FCA' using a generating function and activation
-- function.
--
-- Some common ones include 'logistic' and @'vmap' 'reLU'@.
pattern FCA
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCA i o
pattern FCA { _fcaGen, _fcaActivation } = RM _fcaActivation (FC _fcaGen)

-- | Construct an @'FCA' i o@ using a given distribution from the
-- /statistics/ library.
fca :: ContGen d
    => d
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCA i o
fca d = FCA (genContVar d)

type FCp = LRp

fcWeights :: Lens (FCp i o) (FCp i' o) (L o i) (L o i')
fcWeights = lrBeta

fcBias :: Lens' (FCp i o) (R o)
fcBias = lrAlpha

-- | Fully connected recurrent layer with bias.
--
-- Parameterized by its initialization distributions, and also the function
-- to compute the new state from previous input.
type FCR h i o = Recurrent (R (i + h)) (R i) (R h) (R o) (FC (i + h) o)

pattern FCR
    :: (KnownNat h, KnownNat i)
    => (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m (R h))
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> FCR h i o
pattern FCR { _fcrGen, _fcrGenState, _fcrStore } <-
    Rec { _recInit  = _fcrGenState
        , _recLoop  = _fcrStore
        , _recLearn = FC { _fcGen = _fcrGen }
        }
  where
    FCR g gs s = Rec { _recInit  = gs
                     , _recSplit = H.split
                     , _recJoin  = (H.#)
                     , _recLoop  = s
                     , _recLearn = FC g
                     }

-- | Construct an @'FCR' h i o@ using given distributions from the
-- /statistics/ library.
fcr :: (KnownNat h, KnownNat i, ContGen d, ContGen e)
    => d        -- ^ gen params
    -> e        -- ^ gen history
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> FCR h i o
fcr d e = FCR (genContVar d)
              (fmap vecR . SVS.replicateM . genContVar e)

-- | Convenient synonym for an 'FCR' post-composed with a simple
-- parameterless activation function.
type FCRA h i o = RMap (R o) (R o) (FCR h i o)

-- | Construct an 'FCRA' using a generating function and activation
-- function.
--
-- Some common ones include 'logistic' and @'vmap' 'reLU'@.
pattern FCRA
    :: (KnownNat h, KnownNat i)
    => (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m (R h))
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCRA h i o
pattern FCRA { _fcraGen, _fcraGenState, _fcraStore, _fcraActivation }
    = RM _fcraActivation (FCR _fcraGen _fcraGenState _fcraStore)

-- | Construct an @'FCRA' h i o@ using given distributions from the
-- /statistics/ library.
fcra :: (KnownNat h, KnownNat i, ContGen d, ContGen e)
    => d                -- ^ gen params
    -> e                -- ^ gen state
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCRA h i o
fcra d e = FCRA (genContVar d) (fmap vecR . SVS.replicateM . genContVar e)

type FCRp h i o = FCp (i + h) o

lensIso :: (s -> (a, x)) -> ((b, x) -> t) -> Lens s t a b
lensIso f g h x = g <$> _1 h (f x)

fcrInputWeights
    :: (KnownNat h, KnownNat i, KnownNat i', KnownNat o)
    => Lens (FCRp h i o) (FCRp h i' o) (L o i) (L o i')
fcrInputWeights = fcWeights . lensIso H.splitCols (uncurry (H.|||))

fcrStateWeights
    :: (KnownNat h, KnownNat h', KnownNat i, KnownNat o)
    => Lens (FCRp h i o) (FCRp h' i o) (L o h) (L o h')
fcrStateWeights = fcWeights . lensIso (swap . H.splitCols) (uncurry (H.|||) . swap)

fcrBias :: Lens' (FCRp h i o) (R o)
fcrBias = fcBias

