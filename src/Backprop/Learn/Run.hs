{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Backprop.Learn.Run (
    consecutives
  , consecutivesN
  , leadings
  , conduitLearn, conduitLearnStoch
  -- * Encoding and decoding for learning
  , oneHot', oneHot, oneHotR
  , SVG.maxIndex, maxIndexR
  ) where

import           Backprop.Learn.Model
import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Data.Bool
import           Data.Conduit
import           Data.Finite
import           Data.Foldable
import           Data.Proxy
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static
import           Numeric.LinearAlgebra.Static.Vector
import qualified Data.Conduit.Combinators            as C
import qualified Data.Sequence                       as Seq
import qualified Data.Vector.Generic                 as VG
import qualified Data.Vector.Generic.Sized           as SVG
import qualified System.Random.MWC                   as MWC

consecutives :: Monad m => ConduitT i (i, i) m ()
consecutives = void . runMaybeT $ do
    x <- MaybeT await
    go x
  where
    go x = do
      y <- MaybeT await
      lift $ yield (x, y)
      go y

consecutivesN
    :: forall v n i m. (KnownNat n, VG.Vector v i, Monad m)
    => ConduitT i (SVG.Vector v n i, SVG.Vector v n i) m ()
consecutivesN = conseq (fromIntegral n) .| C.concatMap process
  where
    n = natVal (Proxy @n)
    process (xs, ys, _) = (,) <$> SVG.fromList (toList xs)
                              <*> SVG.fromList (toList ys)

leadings
    :: forall v n i m. (KnownNat n, VG.Vector v i, Monad m)
    => ConduitT i (SVG.Vector v n i, i) m ()
leadings = conseq (fromIntegral n) .| C.concatMap process
  where
    n = natVal (Proxy @n)
    process (xs, _, y) = (, y) <$> SVG.fromList (toList xs)

conseq
    :: forall i m. Monad m
    => Int
    -> ConduitT i (Seq.Seq i, Seq.Seq i, i) m ()
conseq n = void . runMaybeT $ do
    xs <- Seq.replicateM n $ MaybeT await
    go xs
  where
    go xs = do
      _ Seq.:<| xs' <- pure xs
      y <- MaybeT await
      let ys = xs' Seq.:|> y
      lift $ yield (xs, ys, y)
      go ys

conduitLearn
    :: (Learn a b l, Backprop b, MaybeC Backprop (LStateMaybe l), Monad m)
    => l
    -> LParam_ I l
    -> LState_ I l
    -> ConduitT a b m (LState_ I l)
conduitLearn l p = go
  where
    go s = do
      mx <- await
      case mx of
        Nothing -> return s
        Just x  -> do
          let (y, s') = runLearn_ l p x s
          yield y
          go s'

conduitLearnStoch
    :: (Learn a b l, Backprop b, MaybeC Backprop (LStateMaybe l), PrimMonad m)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> LState_ I l
    -> ConduitT a b m (LState_ I l)
conduitLearnStoch l g p = go
  where
    go s = do
      mx <- await
      case mx of
        Nothing -> return s
        Just x  -> do
          (y, s') <- lift $ runLearnStoch_ l g p x s
          yield y
          go s'

-- | What module should this be in?
oneHot'
    :: (VG.Vector v a, KnownNat n)
    => a                -- ^ not hot
    -> a                -- ^ hot
    -> Finite n
    -> SVG.Vector v n a
oneHot' nothot hot i = SVG.generate (bool nothot hot . (== i))

oneHot
    :: (VG.Vector v a, KnownNat n, Num a)
    => Finite n
    -> SVG.Vector v n a
oneHot = oneHot' 0 1

oneHotR :: KnownNat n => Finite n -> R n
oneHotR = vecR . oneHot

-- | Could be in /hmatrix/.
maxIndexR :: KnownNat n => R (n + 1) -> Finite (n + 1)
maxIndexR = SVG.maxIndex . rVec
