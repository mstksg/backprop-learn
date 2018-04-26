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
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Neural.LSTM (
    -- * Basic LSTM
    LSTM, pattern LSTM
  , LSTMp(..), lstmForget, lstmInput, lstmUpdate, lstmOutput
  , LSTM'(..)
    -- * GRU
  , GRU, pattern GRU
  , GRUp(..), gruMemory, gruUpdate, gruOutput
  , GRU'(..)
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

-- | "Base" for 'GRU'.  An 'GRU' is just an 'GRU'' where the second half
-- of the input vector is the previous output.
--
-- This is mostly an implementation detail.  It is recommended that you use
-- 'GRU' and its constructor, instead of directly using this.
data GRU' (i :: Nat) (o :: Nat) = GRU'
  deriving (Typeable)


-- | 'GRU' layer parmateters
data GRUp (i :: Nat) (o :: Nat) =
    GRUp { _gruMemory :: !(FCp (i + o) o)
         , _gruUpdate :: !(FCp (i + o) o)
         , _gruOutput :: !(FCp (i + o) o)
         }
  deriving (Generic, Typeable, Show)

instance NFData (GRUp i o)
instance (KnownNat i, KnownNat o) => Additive (GRUp i o)
instance (KnownNat i, KnownNat o) => Scaling Double (GRUp i o)
instance (KnownNat i, KnownNat o) => Metric Double (GRUp i o)
instance (KnownNat i, KnownNat o, Ref m (GRUp i o) v) => AdditiveInPlace m v (GRUp i o)
instance (KnownNat i, KnownNat o, Ref m (GRUp i o) v) => ScalingInPlace m v Double (GRUp i o)
instance (KnownNat i, KnownNat o) => Bi.Binary (GRUp i o)

instance (KnownNat i, KnownNat o) => Initialize (GRUp i o) where
    initialize d g = GRUp <$> initialize d g
                          <*> initialize d g
                          <*> initialize d g

instance (KnownNat i, KnownNat o) => Num (GRUp i o) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance (KnownNat i, KnownNat o) => Fractional (GRUp i o) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance (KnownNat i, KnownNat o) => Floating (GRUp i o) where
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

gruMemory :: Lens' (GRUp i o) (FCp (i + o) o)
gruMemory f x = (\y -> x { _gruMemory = y }) <$> f (_gruMemory x)

gruUpdate :: Lens' (GRUp i o) (FCp (i + o) o)
gruUpdate f x = (\y -> x { _gruUpdate = y }) <$> f (_gruUpdate x)

gruOutput :: Lens' (GRUp i o) (FCp (i + o) o)
gruOutput f x = (\y -> x { _gruOutput = y }) <$> f (_gruOutput x)

instance (KnownNat i, KnownNat o, KnownNat io, io ~ (i + o)) => Learn (R io) (R o) (GRU' i o) where
    type LParamMaybe (GRU' i o) = 'Just (GRUp i o)
    type LStateMaybe (GRU' i o) = 'Nothing

    runLearn GRU' (J_ p) = stateless $ \x ->
        let z      = logistic $ runLRp (p ^^. gruMemory) x
            r      = logistic $ runLRp (p ^^. gruUpdate) x
            r'     = 1 # r
            h'     = tanh     $ runLRp (p ^^. gruOutput) (r' * x)
        in  (1 - z) * snd (split @i x) + z * h'

-- | Gated Recurrent Unit
--
-- <http://colah.github.io/posts/2015-08-Understanding-LSTMs/>
--
-- @
-- instance 'Learn' ('R' i) (R o) ('GRU' i o) where
--     type 'LParamMaybe' (GRU i o) = ''Just' ('GRUp' i o)
--     type 'LStateMaybe' (GRU i o) = 'Just (R o)
-- @
type GRU i o = Recurrent (R (i + o)) (R i) (R o) (R o) (GRU' i o)

-- | Construct an 'GRU'
pattern GRU :: (KnownNat i, KnownNat o) => GRU i o
pattern GRU <- Rec { _recLearn = GRU' }
  where
    GRU = Rec
      { _recSplit = H.split
      , _recJoin  = (H.#)
      , _recLoop  = id
      , _recLearn = GRU'
      }
