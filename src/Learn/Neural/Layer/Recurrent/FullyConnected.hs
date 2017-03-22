{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Learn.Neural.Layer.Recurrent.FullyConnected (
    RFCLayer
  ) where

import           Data.Kind
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Statistics.Distribution
import           Statistics.Distribution.Normal

data RFCLayer :: Type


instance (KnownNat i, KnownNat o) => Component RFCLayer b (BV i) (BV o) where
    data CParam  RFCLayer b (BV i) (BV o) =
            RFCP { rfcInpWeights   :: !(b (BM o i))
                 , rfcStateWeights :: !(b (BM o o))
                 , rfcBiases       :: !(b (BV o))
                 }
    type CState  RFCLayer b (BV i) (BV o) = 'Just (b (BV o))
    type CConstr RFCLayer b (BV i) (BV o) = (Num (b (BM o i)), Num (b (BM o o)))
    data CConf   RFCLayer b (BV i) (BV o) = forall d. ContGen d => RFCC d

    defConf = RFCC (normalDistr 0 0.5)

