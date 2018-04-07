{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE TypeInType         #-}

module Backprop.Learn.Model.Neural.LSTM (
  ) where

import           Backprop.Learn.Model.Class
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Typeable
import           GHC.Generics                          (Generic)
import           GHC.TypeNats
import           Backprop.Learn.Model.Neural
import           Numeric.LinearAlgebra.Static.Backprop
import qualified System.Random.MWC                     as MWC

-- data LSTM (h :: Nat) (i :: Nat) (o :: Nat) =
--     LSTM { _lstmGen      :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
--          , _lstmGenState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
--          }

-- data LSTMp h i o = LSTMp { _lstmBias  :: !(L o i)
--                          , _fcWeights :: !(L o i)
--                          }
--   deriving (Generic, Typeable, Show)



    -- FCR { _fcrGen      :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
    --     , _fcrGenState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
    --     , _fcrStore    :: forall s. Reifies s W => BVar s (R o) -> BVar s (R h)
    --     }
