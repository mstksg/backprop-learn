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
import           Numeric.BLASTensor
import           Numeric.Backprop
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data FullyConnected :: Type

instance (Num (b (BM o i)), Num (b (BV o))) => Num (CParam FullyConnected b (BV i) (BV o)) where
    FCP w1 b1 + FCP w2 b2 = FCP (w1 + w2) (b1 + b2)
    FCP w1 b1 - FCP w2 b2 = FCP (w1 - w2) (b1 - b2)
    FCP w1 b1 * FCP w2 b2 = FCP (w1 * w2) (b1 * b2)
    negate (FCP w b) = FCP (negate w) (negate b)
    signum (FCP w b) = FCP (signum w) (signum b)
    abs    (FCP w b) = FCP (abs    w) (abs    b)
    fromInteger x = FCP (fromInteger x) (fromInteger x)

instance (Fractional (b (BM o i)), Fractional (b (BV o))) => Fractional (CParam FullyConnected b (BV i) (BV o)) where
    FCP w1 b1 / FCP w2 b2 = FCP (w1 / w2) (b1 / b2)
    recip (FCP w b)       = FCP (recip w) (recip b)
    fromRational x        = FCP (fromRational x) (fromRational x)

instance Num (CState FullyConnected b (BV i) (BV o)) where
    _ + _         = FCS
    _ * _         = FCS
    _ - _         = FCS
    negate _      = FCS
    abs    _      = FCS
    signum _      = FCS
    fromInteger _ = FCS

instance Fractional (CState FullyConnected b (BV i) (BV o)) where
    _ / _          = FCS
    recip _        = FCS
    fromRational _ = FCS



deriving instance Generic (CParam FullyConnected b (BV i) (BV o))
instance SOP.Generic (CParam FullyConnected b (BV i) (BV o))

instance (KnownNat i, KnownNat o) => Component FullyConnected (BV i) (BV o) where
    data CParam  FullyConnected b (BV i) (BV o) =
            FCP { _fcWeights :: !(b (BM o i))
                , _fcBiases  :: !(b (BV o))
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
