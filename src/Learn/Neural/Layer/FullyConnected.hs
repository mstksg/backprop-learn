{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}

module Learn.Neural.Layer.FullyConnected (
) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TypeLits
import           GHC.Generics                   (Generic)
import           Learn.Neural
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso
import           Numeric.Tensor
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data FCLayer :: Type

instance Num (CParam FCLayer b ('BV i) ('BV o))

deriving instance Generic (CParam FCLayer b ('BV i) ('BV o))
instance SOP.Generic (CParam FCLayer b ('BV i) ('BV o))

instance (KnownNat i, KnownNat o) => Component FCLayer ('BV i) ('BV o) where
    data CParam FCLayer b ('BV i) ('BV o) =
            FCP { fcWeights :: !(b ('BM o i))
                , fcBiases  :: !(b ('BV o))
                }
    type CState FCLayer b ('BV i) ('BV o)  = 'Nothing
    type CConstr FCLayer b ('BV i) ('BV o) = Num (b ('BM o i))

    componentOp = bpOp . withInps $ \(x :< p :< Ø) -> do
        w :< b :< Ø <- gTuple #<~ p
        y <- matVecOp ~$ (w :< x :< Ø)
        z <- (+.)     ~$ (y :< b :< Ø)
        return $ only z

    initComponent = \case
      SBV i@SNat -> \case
        so@(SBV o@SNat) -> \g -> do
          w <- genA (SBM o i) $ \_ ->
            realToFrac <$> genContVar (normalDistr 0 0.5) g
          b <- genA so $ \_ ->
            realToFrac <$> genContVar (normalDistr 0 0.5) g
          return . only_ $ FCP w b
