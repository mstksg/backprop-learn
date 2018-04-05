{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}

module Backprop.Learn.Run (
    consecutives
  , consecutivesN
  , leadings
  ) where

import           Control.Monad
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Data.Conduit
import           Data.Foldable
import           Data.Proxy
import           GHC.TypeNats
import qualified Data.Conduit.Combinators  as C
import qualified Data.Sequence             as Seq
import qualified Data.Vector.Generic       as VG
import qualified Data.Vector.Generic.Sized as SVG

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

