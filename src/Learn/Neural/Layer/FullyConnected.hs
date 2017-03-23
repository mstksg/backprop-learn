{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}

module Learn.Neural.Layer.FullyConnected (
    FullyConnected
  ) where

import           Data.Kind
import           Data.Singletons.TypeLits
import           GHC.Generics                   (Generic)
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Tensor
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data FullyConnected :: Type

instance Num (CParam FullyConnected b (BV i) (BV o))
instance Num (CState FullyConnected b (BV i) (BV o))

deriving instance Generic (CParam FullyConnected b (BV i) (BV o))
instance SOP.Generic (CParam FullyConnected b (BV i) (BV o))

instance (KnownNat i, KnownNat o) => Component FullyConnected (BV i) (BV o) where
    data CParam  FullyConnected b (BV i) (BV o) =
            FCP { fcWeights :: !(b (BM o i))
                , fcBiases  :: !(b (BV o))
                }
    data CState  FullyConnected b (BV i) (BV o) = FCS
    type CConstr FullyConnected b (BV i) (BV o) = Num (b (BM o i))
    data CConf   FullyConnected   (BV i) (BV o) = forall d. ContGen d => FCC d

    componentOp = componentOpDefault

    initParam (SBV i) so@(SBV o) (FCC d) g = do
        w <- genA (SBM o i) $ \_ ->
          realToFrac <$> genContVar d g
        b <- genA so $ \_ ->
          realToFrac <$> genContVar d g
        return $ FCP w b

    initState _ _ _ _ = return FCS

    defConf = FCC (normalDistr 0 0.5)

instance (KnownNat i, KnownNat o) => ComponentFF FullyConnected (BV i) (BV o) where
    componentOpFF = bpOp . withInps $ \(x :< p :< Ø) -> do
        w :< b :< Ø <- gTuple #<~ p
        y <- matVecOp ~$ (w :< x :< Ø)
        z <- (+.)     ~$ (y :< b :< Ø)
        return . only $ z

instance (KnownNat i, KnownNat o) => ComponentLayer r FullyConnected (BV i) (BV o) where
    componentRunMode = RMIsFF
