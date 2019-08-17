{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE DeriveAnyClass                           #-}
{-# LANGUAGE DeriveDataTypeable                       #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE DerivingVia                              #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TemplateHaskell                          #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Neural.LSTM (
    -- * LSTM
    lstm
  , LSTMp(..), lstmForget, lstmInput, lstmUpdate, lstmOutput
  , reshapeLSTMpInput
  , reshapeLSTMpOutput
    -- * GRU
  , gru
  , GRUp(..), gruMemory, gruUpdate, gruOutput
  ) where

import           Backprop.Learn.Initialize
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Neural
import           Backprop.Learn.Model.Regression
import           Backprop.Learn.Model.State
import           Backprop.Learn.Model.Types
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Primitive
import           Data.Type.Tuple
import           Data.Typeable
import           GHC.Generics                          (Generic)
import           GHC.TypeNats
import           Lens.Micro
import           Lens.Micro.TH
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update
import           Statistics.Distribution
import qualified Data.Binary                           as Bi
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

-- TODO: allow parameterize internal activation function?
-- TODO: Peepholes

-- | 'LSTM' layer parmateters
data LSTMp (i :: Nat) (o :: Nat) =
    LSTMp { _lstmForget :: !(FCp (i + o) o)
          , _lstmInput  :: !(FCp (i + o) o)
          , _lstmUpdate :: !(FCp (i + o) o)
          , _lstmOutput :: !(FCp (i + o) o)
          }
  deriving stock     (Generic, Typeable, Show)
  deriving anyclass  (NFData, Linear Double, Metric Double, Bi.Binary, Regularize, Backprop)

deriving via (GNum (LSTMp i o)) instance (KnownNat i, KnownNat o) => Num (LSTMp i o)
deriving via (GNum (LSTMp i o)) instance (KnownNat i, KnownNat o) => Fractional (LSTMp i o)
deriving via (GNum (LSTMp i o)) instance (KnownNat i, KnownNat o) => Floating (LSTMp i o)

makeLenses ''LSTMp

instance (PrimMonad m, KnownNat i, KnownNat o) => Mutable m (LSTMp i o) where
    type Ref m (LSTMp i o) = GRef m (LSTMp i o)
    thawRef   = gThawRef
    freezeRef = gFreezeRef
    copyRef   = gCopyRef
instance (PrimMonad m, KnownNat i, KnownNat o) => LinearInPlace m Double (LSTMp i o)

instance (PrimMonad m, KnownNat i, KnownNat o) => Learnable m (LSTMp i o)

lstm'
    :: (KnownNat i, KnownNat o)
    => Model ('Just (LSTMp i o)) ('Just (R o)) (R (i + o)) (R o)
lstm' = modelD $ \(PJust p) x (PJust s) ->
    let forget = logistic $ runLRp (p ^^. lstmForget) x
        input  = logistic $ runLRp (p ^^. lstmInput ) x
        update = tanh     $ runLRp (p ^^. lstmUpdate) x
        s'     = forget * s + input * update
        o      = logistic $ runLRp (p ^^. lstmOutput) x
        h      = o * tanh s'
    in  (h, PJust s')

-- | Long-term short-term memory layer
--
-- <http://colah.github.io/posts/2015-08-Understanding-LSTMs/>
--
lstm
    :: (KnownNat i, KnownNat o)
    => Model ('Just (LSTMp i o)) ('Just (R o :# R o)) (R i) (R o)
lstm = recurrent H.split (H.#) id lstm'

reshapeLSTMpInput
    :: (ContGen d, PrimMonad m, KnownNat i, KnownNat i', KnownNat o)
    => d
    -> MWC.Gen (PrimState m)
    -> LSTMp i o
    -> m (LSTMp i' o)
reshapeLSTMpInput d g (LSTMp forget input update output) =
    LSTMp <$> reshaper forget
          <*> reshaper input
          <*> reshaper update
          <*> reshaper output
  where
    reshaper = reshapeLRpInput d g

reshapeLSTMpOutput
    :: (ContGen d, PrimMonad m, KnownNat i, KnownNat o, KnownNat o')
    => d
    -> MWC.Gen (PrimState m)
    -> LSTMp i o
    -> m (LSTMp i o')
reshapeLSTMpOutput d g (LSTMp forget input update output) =
    LSTMp <$> reshaper forget
          <*> reshaper input
          <*> reshaper update
          <*> reshaper output
  where
    reshaper = reshapeLRpInput  d g
           <=< reshapeLRpOutput d g

-- | Forget biases initialized to 1
instance (KnownNat i, KnownNat o) => Initialize (LSTMp i o) where
    initialize d g = LSTMp <$> set (mapped . fcBias) 1 (initialize d g)
                           <*> initialize d g
                           <*> initialize d g
                           <*> initialize d g

-- | 'GRU' layer parmateters
data GRUp (i :: Nat) (o :: Nat) =
    GRUp { _gruMemory :: !(FCp (i + o) o)
         , _gruUpdate :: !(FCp (i + o) o)
         , _gruOutput :: !(FCp (i + o) o)
         }
  deriving stock     (Generic, Typeable, Show)
  deriving anyclass  (NFData, Linear Double, Metric Double, Bi.Binary, Initialize, Regularize, Backprop)

deriving via (GNum (GRUp i o)) instance (KnownNat i, KnownNat o) => Num (GRUp i o)
deriving via (GNum (GRUp i o)) instance (KnownNat i, KnownNat o) => Fractional (GRUp i o)
deriving via (GNum (GRUp i o)) instance (KnownNat i, KnownNat o) => Floating (GRUp i o)

makeLenses ''GRUp

instance (PrimMonad m, KnownNat i, KnownNat o) => Mutable m (GRUp i o) where
    type Ref m (GRUp i o) = GRef m (GRUp i o)
    thawRef   = gThawRef
    freezeRef = gFreezeRef
    copyRef   = gCopyRef
instance (KnownNat i, KnownNat o, Mutable m (GRUp i o)) => LinearInPlace m Double (GRUp i o)

instance (KnownNat i, KnownNat o, PrimMonad m) => Learnable m (GRUp i o)

gru'
    :: forall i o. (KnownNat i, KnownNat o)
    => Model ('Just (GRUp i o)) 'Nothing (R (i + o)) (R o)
gru' = modelStatelessD $ \(PJust p) x ->
    let z      = logistic $ runLRp (p ^^. gruMemory) x
        r      = logistic $ runLRp (p ^^. gruUpdate) x
        r'     = 1 # r
        h'     = tanh     $ runLRp (p ^^. gruOutput) (r' * x)
    in  (1 - z) * snd (split @i x) + z * h'

-- | Gated Recurrent Unit
--
-- <http://colah.github.io/posts/2015-08-Understanding-LSTMs/>
--
gru :: (KnownNat i, KnownNat o)
    => Model ('Just (GRUp i o)) ('Just (R o)) (R i) (R o)
gru = recurrent H.split (H.#) id gru'
