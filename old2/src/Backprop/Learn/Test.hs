{-# LANGUAGE ApplicativeDo                        #-}
{-# LANGUAGE FlexibleContexts                     #-}
{-# LANGUAGE PartialTypeSignatures                #-}
{-# LANGUAGE RankNTypes                           #-}
{-# LANGUAGE ScopedTypeVariables                  #-}
{-# LANGUAGE TypeApplications                     #-}
{-# LANGUAGE TypeFamilies                         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Backprop.Learn.Test (
  -- * Tests
    Test
  , maxIxTest, rmseTest
  , squaredErrorTest, absErrorTest, totalSquaredErrorTest, squaredErrorTestV
  , crossEntropyTest
  -- ** Manipulate tests
  , lossTest, lmapTest
  -- * Run tests
  , testLearn, testLearnStoch, testLearnAll, testLearnStochAll
  -- ** Correlation tests
  , testLearnCov, testLearnCorr
  , testLearnStochCov, testLearnStochCorr
  ) where

import           Backprop.Learn.Loss
import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Function
import           Data.Profunctor
import           Data.Proxy
import           GHC.TypeNats
import           Numeric.Backprop
import qualified Control.Foldl                as L
import qualified Numeric.LinearAlgebra        as HU
import qualified Numeric.LinearAlgebra.Static as H
import qualified System.Random.MWC            as MWC

-- TODO: support non-double results?

type Test o = o -> o -> Double

-- | Create a 'Test' from a 'Loss'
lossTest :: Loss a -> Test a
lossTest l x = evalBP (l x)

maxIxTest :: KnownNat n => Test (H.R n)
maxIxTest x y
    | match x y = 1
    | otherwise = 0
  where
    match = (==) `on` (HU.maxIndex . H.extract)

rmseTest :: forall n. KnownNat n => Test (H.R n)
rmseTest x y = H.norm_2 (x - y) / sqrt (fromIntegral (natVal (Proxy @n)))

squaredErrorTest :: Real a => Test a
squaredErrorTest x y = e * e
  where
    e = realToFrac (x - y)

absErrorTest :: Real a => Test a
absErrorTest x y = realToFrac . abs $ x - y

totalSquaredErrorTest :: (Applicative t, Foldable t, Real a) => Test (t a)
totalSquaredErrorTest x y = realToFrac (sum e)
  where
    e = do
      x' <- x
      y' <- y
      pure ((x' - y') ^ (2 :: Int))

squaredErrorTestV :: KnownNat n => Test (H.R n)
squaredErrorTestV x y = e `H.dot` e
  where
    e = x - y

crossEntropyTest :: KnownNat n => Test (H.R n)
crossEntropyTest targ res = -(log res H.<.> targ)

lmapTest
    :: (a -> b)
    -> Test b
    -> Test a
lmapTest f t x y = t (f x) (f y)

testLearn
    :: (Learn a b l, NoState l)
    => Test b
    -> l
    -> LParam_ I l
    -> a
    -> b
    -> Double
testLearn t l mp x y = t y $ runLearnStateless_ l mp x

testLearnStoch
    :: (Learn a b l, NoState l, PrimMonad m)
    => Test b
    -> l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> a
    -> b
    -> m Double
testLearnStoch t l g mp x y = t y <$> runLearnStochStateless_ l g mp x

cov :: Fractional a => L.Fold (a, a) a
cov = do
    x  <- lmap fst           L.sum
    y  <- lmap snd           L.sum
    xy <- lmap (uncurry (*)) L.sum
    n  <- fromIntegral <$> L.length
    pure (xy / n - (x * y) / n / n)

corr :: Floating a => L.Fold (a, a) a
corr = do
    x  <- lmap fst           L.sum
    x2 <- lmap ((**2) . fst) L.sum
    y  <- lmap snd           L.sum
    y2 <- lmap ((**2) . snd) L.sum
    xy <- lmap (uncurry (*)) L.sum
    n  <- fromIntegral <$> L.length
    pure $ (xy / n - (x * y) / n / n)
         / sqrt ( x2 / n - (x / n)**2 )
         / sqrt ( y2 / n - (y / n)**2 )

testLearnCov
    :: (Learn a b l, NoState l, Foldable t, Fractional b)
    => l
    -> LParam_ I l
    -> t (a, b)
    -> b
testLearnCov l p = L.fold $ (lmap . first) (runLearnStateless_ l p) cov

testLearnCorr
    :: (Learn a b l, NoState l, Foldable t, Floating b)
    => l
    -> LParam_ I l
    -> t (a, b)
    -> b
testLearnCorr l p = L.fold $ (lmap . first) (runLearnStateless_ l p) corr

testLearnAll
    :: (Learn a b l, NoState l, Foldable t)
    => Test b
    -> l
    -> LParam_ I l
    -> t (a, b)
    -> Double
testLearnAll t l p = L.fold $ lmap (uncurry (testLearn t l p)) L.mean

-- newtype M m a = M { getM :: m a }
-- instance (Semigroup a, Applicative m) => Semigroup (M m a) where
--     M x <> M y = M $ liftA2 (<>) x y
-- instance (Monoid a, Applicative m) => Monoid (M m a) where
--     mappend = (<>)
--     mempty = M (pure mempty)

testLearnStochAll
    :: (Learn a b l, NoState l, PrimMonad m, Foldable t)
    => Test b
    -> l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> t (a, b)
    -> m Double
testLearnStochAll t l g p = L.foldM $ L.premapM (uncurry (testLearnStoch t l g p))
                                      (L.generalize L.mean)

testLearnStochCov
    :: (Learn a b l, NoState l, PrimMonad m, Foldable t, Fractional b)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> t (a, b)
    -> m b
testLearnStochCov l g p = L.foldM $ (L.premapM . flip bitraverse pure)
                                      (runLearnStochStateless_ l g p)
                                      (L.generalize cov)

testLearnStochCorr
    :: (Learn a b l, NoState l, PrimMonad m, Foldable t, Floating b)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> t (a, b)
    -> m b
testLearnStochCorr l g p = L.foldM $ (L.premapM . flip bitraverse pure)
                                       (runLearnStochStateless_ l g p)
                                       (L.generalize corr)
