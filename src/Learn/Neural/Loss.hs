{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE GADTs      #-}
{-# LANGUAGE PolyKinds  #-}
{-# LANGUAGE RankNTypes #-}

module Learn.Neural.Loss (
    LossFunction
  , crossEntropy
  , squaredError
  ) where

import           GHC.TypeLits
import           Numeric.BLAS
import           Numeric.Backprop

-- type LossFunction s = forall b q. (BLAS b, Num (b s)) => b s -> OpB q '[ b s ] '[ Scalar b ]
type LossFunction as b = forall s. Tuple as -> OpB s as '[ b ]

crossEntropy
    :: forall b n. (BLAS b, KnownNat n, Num (b '[n]))
    => LossFunction '[ b '[n] ] (Scalar b)
crossEntropy (I targ :< Ø) = bpOp . withInps $ \(r :< Ø) -> do
    logR <- tmapOp log ~$ (r :< Ø)
    res  <- negate <$> (dotOp ~$ (logR :< t :< Ø))
    only <$> bindVar res
  where
    t = constVar targ

squaredError
    :: (BLAS b, KnownNat n, Num (b '[n]))
    => LossFunction '[ b '[n] ] (Scalar b)
squaredError (I targ :< Ø) = bpOp . withInps $ \(r :< Ø) -> do
    err  <- bindVar $ r - t
    only <$> (dotOp ~$ (err :< err :< Ø))
  where
    t = constVar targ

