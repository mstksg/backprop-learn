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
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           GHC.Generics                   (Generic)
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data FullyConnected :: Type

instance (Num (b '[o,i]), Num (b '[o])) => Num (CParam FullyConnected b '[i] '[o]) where
    FCP w1 b1 + FCP w2 b2 = FCP (w1 + w2) (b1 + b2)
    FCP w1 b1 - FCP w2 b2 = FCP (w1 - w2) (b1 - b2)
    FCP w1 b1 * FCP w2 b2 = FCP (w1 * w2) (b1 * b2)
    negate (FCP w b) = FCP (negate w) (negate b)
    signum (FCP w b) = FCP (signum w) (signum b)
    abs    (FCP w b) = FCP (abs    w) (abs    b)
    fromInteger x = FCP (fromInteger x) (fromInteger x)

instance (Fractional (b '[o,i]), Fractional (b '[o])) => Fractional (CParam FullyConnected b '[i] '[o]) where
    FCP w1 b1 / FCP w2 b2 = FCP (w1 / w2) (b1 / b2)
    recip (FCP w b)       = FCP (recip w) (recip b)
    fromRational x        = FCP (fromRational x) (fromRational x)

instance (Floating (b '[o,i]), Floating (b '[o])) => Floating (CParam FullyConnected b '[i] '[o]) where
    sqrt (FCP w b)       = FCP (sqrt w) (sqrt b)

instance Num (CState FullyConnected b '[i] '[o]) where
    _ + _         = FCS
    _ * _         = FCS
    _ - _         = FCS
    negate _      = FCS
    abs    _      = FCS
    signum _      = FCS
    fromInteger _ = FCS

instance Fractional (CState FullyConnected b '[i] '[o]) where
    _ / _          = FCS
    recip _        = FCS
    fromRational _ = FCS

instance Floating (CState FullyConnected b '[i] '[o]) where
    sqrt _ = FCS





deriving instance Generic (CParam FullyConnected b '[i] '[o])
instance SOP.Generic (CParam FullyConnected b '[i] '[o])

instance (BLAS b, KnownNat i, KnownNat o, Floating (b '[o,i]), Floating (b '[o]))
        => Component FullyConnected b '[i] '[o] where
    data CParam  FullyConnected b '[i] '[o] =
            FCP { _fcWeights :: !(b '[o,i])
                , _fcBiases  :: !(b '[o])
                }
    data CState  FullyConnected b '[i] '[o] = FCS
    type CConstr FullyConnected b '[i] '[o] = Num (b '[o,i])
    data CConf   FullyConnected b '[i] '[o] = forall d. ContGen d => FCC d

    componentOp = componentOpDefault

    initParam = \case
      i `SCons` SNil -> \case
        so@(o `SCons` SNil) -> \(FCC d) g -> do
          w <- genA (o `SCons` (i `SCons` SNil)) $ \_ ->
            realToFrac <$> genContVar d g
          b <- genA so $ \_ ->
            realToFrac <$> genContVar d g
          return $ FCP w b
        _ -> error "inaccessible."
      _ -> error "inaccessible."

    initState _ _ _ _ = return FCS

    defConf = FCC (normalDistr 0 0.5)

instance (BLAS b, KnownNat i, KnownNat o, Floating (b '[o,i]), Floating (b '[o]))
        => ComponentFF FullyConnected b '[i] '[o] where
    componentOpFF = bpOp . withInps $ \(x :< p :< Ø) -> do
        w :< b :< Ø <- gTuple #<~ p
        y <- matVecOp ~$ (w :< x :< Ø)
        z <- (+.)     ~$ (y :< b :< Ø)
        return . only $ z

instance (BLAS b, KnownNat i, KnownNat o, Floating (b '[o,i]), Floating (b '[o]))
        => ComponentLayer r FullyConnected b '[i] '[o] where
    componentRunMode = RMIsFF
