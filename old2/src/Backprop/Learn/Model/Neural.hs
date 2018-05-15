{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Neural (
  -- * Fully connected
  -- ** Feed-forward
    FC, pattern FC, FCp, fcBias, fcWeights
  -- *** With activation function
  , FCA, pattern FCA, _fcaActivation
  -- ** Recurrent
  , FCR, pattern FCR, FCRp, fcrBias, fcrInputWeights, fcrStateWeights
  -- *** With activation function
  , FCRA, pattern FCRA, _fcraStore, _fcraActivation
  ) where


import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Regression
import           Backprop.Learn.Model.State
import           Data.Tuple
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import qualified Numeric.LinearAlgebra.Static          as H

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

pattern FC :: FC i o
pattern FC = LinReg

-- | Convenient synonym for an 'FC' post-composed with a simple
-- parameterless activation function.
type FCA i o = RMap (R o) (R o) (FC i o)

-- | Construct an 'FCA' using a generating function and activation
-- function.
--
-- Some common ones include 'logistic' and @'vmap' 'reLU'@.
pattern FCA
    :: (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))          -- ^ '_fcaActivation'
    -> FCA i o
pattern FCA { _fcaActivation } = RM _fcaActivation FC

type FCp = LRp

fcWeights :: Lens (FCp i o) (FCp i' o) (L o i) (L o i')
fcWeights = lrBeta

fcBias :: Lens' (FCp i o) (R o)
fcBias = lrAlpha

-- | Fully connected recurrent layer with bias.
--
-- Parameterized by its initialization distributions, and also the function
-- to compute the new state from previous input.
--
-- @
-- instance 'Learn' ('R' i) (R o) ('FCR' h i o) where
--     type 'LParamMaybe' (FCR h i o) = ''Just' ('FCRp' h i o)
--     type 'LStateMaybe' (FCR h i o) = 'Just (R h)
-- @
type FCR h i o = Recurrent (R (i + h)) (R i) (R h) (R o) (FC (i + h) o)

-- | Construct an 'FCR'
pattern FCR
    :: (KnownNat h, KnownNat i)
    => (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))          -- ^ '_fcrSTore'
    -> FCR h i o
pattern FCR { _fcrStore } <-
    Rec { _recLoop  = _fcrStore
        , _recLearn = FC
        }
  where
    FCR s = Rec { _recSplit = H.split
                , _recJoin  = (H.#)
                , _recLoop  = s
                , _recLearn = FC
                }
{-# COMPLETE FCR #-}

-- | Convenient synonym for an 'FCR' post-composed with a simple
-- parameterless activation function.
type FCRA h i o = RMap (R o) (R o) (FCR h i o)

-- | Construct an 'FCRA' using a generating function and activation
-- function.
--
-- Some common ones include 'logistic' and @'vmap' 'reLU'@.
pattern FCRA
    :: (KnownNat h, KnownNat i)
    => (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))          -- ^ '_fcraStore'
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))          -- ^ '_fcraActivation'
    -> FCRA h i o
pattern FCRA { _fcraStore, _fcraActivation }
    = RM _fcraActivation (FCR _fcraStore)

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

