{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Learn.Neural.Layer.Recurrent.FullyConnected (
    RFullyConnected
  ) where

import           Data.Kind
import           GHC.Generics                   (Generic)
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso           (iso)
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data RFullyConnected :: Type

deriving instance Generic (CParam RFullyConnected b (BV i) (BV o))
instance SOP.Generic (CParam RFullyConnected b (BV i) (BV o))

instance Num (CParam RFullyConnected b (BV i) (BV o))
instance Num (CState RFullyConnected b (BV i) (BV o))

instance (KnownNat i, KnownNat o) => Component RFullyConnected (BV i) (BV o) where
    data CParam  RFullyConnected b (BV i) (BV o) =
            RFCP { rfcInpWeights   :: !(b (BM o i))
                 , rfcStateWeights :: !(b (BM o o))
                 , rfcBiases       :: !(b (BV o))
                 }
    data CState  RFullyConnected b (BV i) (BV o) = RFCS { rfcState :: !(b (BV o)) }
    type CConstr RFullyConnected b (BV i) (BV o) = (Num (b (BM o i)), Num (b (BM o o)))
    data CConf   RFullyConnected   (BV i) (BV o) = forall d. ContGen d => RFCC d

    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        wI :< wS :< b :< Ø <- gTuple #<~ p
        s0 <- opIso (iso rfcState RFCS) ~$ (s :< Ø)
        y  <- matVecOp ~$ (wI :< x  :< Ø)
        s1 <- matVecOp ~$ (wS :< s0 :< Ø)
        z  <- bindVar $ y + s1 + b
        s' <- opIso (iso RFCS rfcState) ~$ (s0 :< Ø)
        return $ z :< s' :< Ø

    defConf = RFCC (normalDistr 0 0.5)
    initParam (SBV i) so@(SBV o) (RFCC d) g = do
        wI <- genA (SBM o i) $ \_ ->
          realToFrac <$> genContVar d g
        wS <- genA (SBM o o) $ \_ ->
          realToFrac <$> genContVar d g
        b <- genA so $ \_ ->
          realToFrac <$> genContVar d g
        return $ RFCP wI wS b
    initState _ so (RFCC d) g =
        RFCS <$> genA so (\_ -> realToFrac <$> genContVar d g)

instance (KnownNat i, KnownNat o) => ComponentLayer 'Recurrent RFullyConnected (BV i) (BV o) where
    componentRunMode = RMNotFF
