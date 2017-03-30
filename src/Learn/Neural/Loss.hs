{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Learn.Neural.Loss (
    LossFunction
  , crossEntropy
  , squaredError
  , sumLoss
  , zipLoss
  ) where

import           Data.Type.Util
import           Data.Type.Vector
import           GHC.TypeLits
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           Type.Class.Witness
import qualified Data.Type.Nat       as TCN

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

sumLoss
    :: forall n a b. (Num a, Num b)
    => LossFunction '[ a ] b
    -> TCN.Nat n
    -> LossFunction (Replicate n a) b
sumLoss l = \case
    TCN.Z_ -> \case Ø -> op0 (only_ 0)
    TCN.S_ n -> \case
      I x :< xs -> (replLen @_ @a n          //) $
                   (replWit @_ @Num @a n Wit //) $
                bpOp . withInps $ \(y :< ys) -> do
        z  <- l (only_ x) ~$ (y :< Ø)
        zs <- sumLoss l n xs ~$ ys
        return . only $ z + zs

zipLoss
    :: forall n a b. (Num a, Num b)
    => LossFunction '[ a ] b
    -> Vec n b
    -> LossFunction (Replicate n a) b
zipLoss l = \case
    ØV        -> \case Ø -> op0 (only 0)
    I α :* αs ->
      let αn = vecLenNat αs
      in  \case
          I x :< xs -> (replLen @_ @a αn          //) $
                       (replWit @_ @Num @a αn Wit //) $
                bpOp . withInps $ \(y :< ys) -> do
            z  <- l (only_ x) ~$ (y :< Ø)
            zs <- zipLoss l αs xs ~$ ys
            return . only $ (z * constVar α) + zs
