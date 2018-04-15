{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE DeriveDataTypeable                       #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Neural.LSTM (
    LSTM, pattern LSTM
  , LSTMp(..), lstmForget, lstmInput, lstmUpdate, lstmOutput
  , LSTM'(..)
  ) where

import           Backprop.Learn.Initialize
import           Backprop.Learn.Model.Class
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Neural
import           Backprop.Learn.Model.Regression
import           Backprop.Learn.Model.State
import           Control.DeepSeq
import           Data.Typeable
import           GHC.Generics                          (Generic)
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update
import qualified Data.Binary                           as Bi
import qualified Numeric.LinearAlgebra.Static          as H

-- | "Base" for 'LSTM'.  An 'LSTM' is just an 'LSTM'' where the second half
-- of the input vector is the previous output.
--
-- This is mostly an implementation detail.  It is recommended that you use
-- 'LSTM' and its constructor, instead of directly using this.
data LSTM' (i :: Nat) (o :: Nat) = LSTM'
  deriving (Typeable)

-- TODO: allow parameterize internal activation function?
-- TODO: Peepholes

-- | 'LSTM' layer parmateters
data LSTMp (i :: Nat) (o :: Nat) =
    LSTMp { _lstmForget :: !(FCp (i + o) o)
          , _lstmInput  :: !(FCp (i + o) o)
          , _lstmUpdate :: !(FCp (i + o) o)
          , _lstmOutput :: !(FCp (i + o) o)
          }
  deriving (Generic, Typeable, Show)

instance NFData (LSTMp i o)
instance (KnownNat i, KnownNat o) => Additive (LSTMp i o)
instance (KnownNat i, KnownNat o) => Scaling Double (LSTMp i o)
instance (KnownNat i, KnownNat o) => Metric Double (LSTMp i o)
instance (KnownNat i, KnownNat o, Ref m (LSTMp i o) v) => AdditiveInPlace m v (LSTMp i o)
instance (KnownNat i, KnownNat o, Ref m (LSTMp i o) v) => ScalingInPlace m v Double (LSTMp i o)
instance (KnownNat i, KnownNat o) => Bi.Binary (LSTMp i o)

-- | Forget biases initialized to 1
instance (KnownNat i, KnownNat o) => Initialize (LSTMp i o) where
    initialize d g = LSTMp <$> set (mapped . fcBias) 1 (initialize d g)
                           <*> initialize d g
                           <*> initialize d g
                           <*> initialize d g

instance (KnownNat i, KnownNat o) => Num (LSTMp i o) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance (KnownNat i, KnownNat o) => Fractional (LSTMp i o) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance (KnownNat i, KnownNat o) => Floating (LSTMp i o) where
    pi    = gPi
    sqrt  = gSqrt
    exp   = gExp
    log   = gLog
    sin   = gSin
    cos   = gCos
    asin  = gAsin
    acos  = gAcos
    atan  = gAtan
    sinh  = gSinh
    cosh  = gCosh
    asinh = gAsinh
    acosh = gAcosh
    atanh = gAtanh

lstmForget :: Lens' (LSTMp i o) (FCp (i + o) o)
lstmForget f x = (\y -> x { _lstmForget = y }) <$> f (_lstmForget x)

lstmInput :: Lens' (LSTMp i o) (FCp (i + o) o)
lstmInput f x = (\y -> x { _lstmInput = y }) <$> f (_lstmInput x)

lstmUpdate :: Lens' (LSTMp i o) (FCp (i + o) o)
lstmUpdate f x = (\y -> x { _lstmUpdate = y }) <$> f (_lstmUpdate x)

lstmOutput :: Lens' (LSTMp i o) (FCp (i + o) o)
lstmOutput f x = (\y -> x { _lstmOutput = y }) <$> f (_lstmOutput x)

instance (KnownNat i, KnownNat o, KnownNat io, io ~ (i + o)) => Learn (R io) (R o) (LSTM' i o) where
    type LParamMaybe (LSTM' i o) = 'Just (LSTMp i o)
    type LStateMaybe (LSTM' i o) = 'Just (R o)

    runLearn LSTM' (J_ p) x (J_ s) = (h, J_ s')
      where
        forget = logistic $ runLRp (p ^^. lstmForget) x
        input  = logistic $ runLRp (p ^^. lstmInput ) x
        update = tanh     $ runLRp (p ^^. lstmUpdate) x
        s'     = forget * s + input * update
        o      = logistic $ runLRp (p ^^. lstmOutput) x
        h      = o * tanh s'

-- | Long-term short-term memory layer
--
-- <http://colah.github.io/posts/2015-08-Understanding-LSTMs/>
--
-- @
-- instance 'Learn' ('R' i) (R o) ('LSTM' i o) where
--     type 'LParamMaybe' (LSTM i o) = ''Just' ('LSTMp' i o)
--     type 'LStateMaybe' (LSTM i o) = 'Just ('T2' (R o) (R o))     -- cell state, hidden state
-- @
type LSTM i o = Recurrent (R (i + o)) (R i) (R o) (R o) (LSTM' i o)

-- | Construct an 'LSTM'
pattern LSTM :: (KnownNat i, KnownNat o) => LSTM i o
pattern LSTM <- Rec { _recLearn = LSTM' }
  where
    LSTM = Rec
      { _recSplit = H.split
      , _recJoin  = (H.#)
      , _recLoop  = id
      , _recLearn = LSTM'
      }
