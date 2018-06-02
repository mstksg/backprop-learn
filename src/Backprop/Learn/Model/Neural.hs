{-# LANGUAGE AllowAmbiguousTypes                      #-}
{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Neural (
    -- * Feed-forward
    FCp, fc, fca
  , fcWeights, fcBias
    -- * Recurrent
  , fcr, fcra
  , FCRp, fcrBias, fcrInputWeights, fcrStateWeights
  ) where


import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Regression
import           Backprop.Learn.Model.State
import           Backprop.Learn.Model.Types
import           Data.Tuple
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import qualified Numeric.LinearAlgebra.Static          as H

-- | Parameters for fully connected feed-forward layer with bias.
type FCp = LRp

fcWeights :: Lens (FCp i o) (FCp i' o) (L o i) (L o i')
fcWeights = lrBeta

fcBias :: forall i o. Lens' (FCp i o) (R o)
fcBias = lrAlpha

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
-- essentially multivariate logistic regression. (See 'logReg')
fc  :: (KnownNat i, KnownNat o)
    => Model ('Just (FCp i o)) 'Nothing (R i) (R o)
fc = linReg

-- | Convenient synonym for an 'fC' post-composed with a simple
-- parameterless activation function.
fca :: (KnownNat i, KnownNat o)
    => (forall z. Reifies z W => BVar z (R o) -> BVar z (R o))
    -> Model ('Just (FCp i o)) 'Nothing (R i) (R o)
fca f = funcD f <~ linReg

-- | Fully connected recurrent layer with bias.
fcr :: (KnownNat i, KnownNat o, KnownNat s)
    => (forall z. Reifies z W => BVar z (R o) -> BVar z (R s))      -- ^ store
    -> Model ('Just (FCRp s i o)) ('Just (R s)) (R i) (R o)
fcr s = recurrent H.split (H.#) s fc

-- | Convenient synonym for an 'fcr' post-composed with a simple
-- parameterless activation function.
fcra
    :: (KnownNat i, KnownNat o, KnownNat s)
    => (forall z. Reifies z W => BVar z (R o) -> BVar z (R o))
    -> (forall z. Reifies z W => BVar z (R o) -> BVar z (R s))      -- ^ store
    -> Model ('Just (FCRp s i o)) ('Just (R s)) (R i) (R o)
fcra f s = funcD f <~ recurrent H.split (H.#) s fc

-- | Parameter for fully connected recurrent layer.
type FCRp s i o = FCp (i + s) o

lensIso :: (s -> (a, x)) -> ((b, x) -> t) -> Lens s t a b
lensIso f g h x = g <$> _1 h (f x)

fcrInputWeights
    :: (KnownNat s, KnownNat i, KnownNat i', KnownNat o)
    => Lens (FCRp s i o) (FCRp s i' o) (L o i) (L o i')
fcrInputWeights = fcWeights
                . lensIso H.splitCols (uncurry (H.|||))

fcrStateWeights
    :: (KnownNat s, KnownNat s', KnownNat i, KnownNat o)
    => Lens (FCRp s i o) (FCRp s' i o) (L o s) (L o s')
fcrStateWeights = fcWeights
                . lensIso (swap . H.splitCols) (uncurry (H.|||) . swap)

fcrBias :: forall s i o. Lens' (FCRp s i o) (R o)
fcrBias = fcBias @(i + s) @o
