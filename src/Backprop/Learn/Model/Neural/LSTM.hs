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
    LSTM, pattern LSTM, lstm, _lstmGen, _lstmGenCell, _lstmGenState
  , LSTMp(..), lstmForget , lstmInput, lstmUpdate, lstmOutput
  , LSTM'(..)
  ) where

import           Backprop.Learn.Model.Class
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Neural
import           Backprop.Learn.Model.Regression
import           Backprop.Learn.Model.State
import           Control.DeepSeq
import           Control.Monad.Primitive
import           Data.Typeable
import           GHC.Generics                          (Generic)
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update
import           Statistics.Distribution
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

-- | "Base" for 'LSTM'.  An 'LSTM' is just an 'LSTM'' where the second half
-- of the input vector is the previous output.
--
-- This is mostly an implementation detail.  It is recommended that you use
-- 'LSTM' and its constructor, instead of directly using this.
data LSTM' (i :: Nat) (o :: Nat) =
    LSTM' { _lstmGen'     :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
          , _lstmGenCell' :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
          }
  deriving (Typeable)

-- TODO: allow parameterize internal activation function?

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

    initParam LSTM'{..} g = J_ $
        LSTMp <$> fromJ_ (initParam (FC _lstmGen') g)
              <*> fromJ_ (initParam (FC _lstmGen') g)
              <*> fromJ_ (initParam (FC _lstmGen') g)
              <*> fromJ_ (initParam (FC _lstmGen') g)
    initState LSTM'{..} = J_ . fmap vecR . SVS.replicateM . _lstmGenCell'

    runLearn LSTM'{..} (J_ p) x (J_ s) = (h, J_ s')
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
--     type 'LStateMaybe' (LSTM i o) = 'Just ('T2' (R o) (R o))
-- @
type LSTM i o = Recurrent (R (i + o)) (R i) (R o) (R o) (LSTM' i o)

-- | Construct an 'LSTM'
pattern LSTM
    :: (KnownNat i, KnownNat o)
    => (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)     -- ^ '_lstmGen'
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)     -- ^ '_lstmGenCell'
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m (R o))      -- ^ '_lstmGenState'
    -> LSTM i o
pattern LSTM { _lstmGen, _lstmGenCell, _lstmGenState } <-
    Rec { _recInit  = _lstmGenState
        , _recLearn = LSTM' { _lstmGen'     = _lstmGen
                            , _lstmGenCell' = _lstmGenCell
                            }
        }
  where
    LSTM g gc gs = Rec { _recInit  = gs
                       , _recSplit = H.split
                       , _recJoin  = (H.#)
                       , _recLoop  = id
                       , _recLearn = LSTM' { _lstmGen'     = g
                                           , _lstmGenCell' = gc
                                           }
                       }

-- | Convenient wrapper over 'LSTM' constructor taking distributions from
-- 'Statistics.Distribution'.
lstm
    :: (KnownNat i, KnownNat o, ContGen d, ContGen e, ContGen f)
    => d                    -- ^ generate parameters
    -> e                    -- ^ generate initial cell state
    -> f                    -- ^ generate initial history
    -> LSTM i o
lstm d e f = LSTM (genContVar d) (genContVar e)
                  (fmap vecR . SVS.replicateM . genContVar f)
