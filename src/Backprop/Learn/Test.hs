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
  , lmapTest
  -- * Run tests
  , testLearn, testLearnStoch, testLearnAll, testLearnStochAll
  -- ** Correlation tests
  , testLearnCov, testLearnCorr
  , testLearnStochCov, testLearnStochCorr
  ) where

import           Backprop.Learn.Model
import           Control.Applicative
import           Control.Monad.Primitive
import           Data.Function
import           Data.Proxy
import           Data.Semigroup
import           GHC.TypeNats
import           Numeric.Backprop.Tuple
import qualified Numeric.LinearAlgebra        as HU
import qualified Numeric.LinearAlgebra.Static as H
import qualified System.Random.MWC            as MWC

-- TODO: support non-double results?

type Test o = o -> o -> Double

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

testLearnCov
    :: (Learn a b l, NoState l, Foldable t, Fractional b)
    => l
    -> LParam_ I l
    -> t (a, b)
    -> b
testLearnCov l p = process . getSum . foldMap go
  where
    process (T3 (T2 x y) xy n) = xy / n - (x * y) / n / n
    go (x, y) = Sum $ T3 (T2 r y) (r * y) 1
      where
        r  = runLearnStateless_ l p x

testLearnCorr
    :: (Learn a b l, NoState l, Foldable t, Floating b)
    => l
    -> LParam_ I l
    -> t (a, b)
    -> b
testLearnCorr l p = process . getSum . foldMap go
  where
    process (T3 (T2 (T2 x x2) (T2 y y2)) xy n) = (xy / n - (x * y) / n / n)
            / sqrt ( x2 / n - (x / n)**2 )
            / sqrt ( y2 / n - (y / n)**2 )
    go (x, y) = Sum $ T3 (T2 (T2 r (r**2)) (T2 y (y**2))) (r * y) 1
      where
        r  = runLearnStateless_ l p x

testLearnAll
    :: (Learn a b l, NoState l, Foldable t)
    => Test b
    -> l
    -> LParam_ I l
    -> t (a, b)
    -> Double
testLearnAll t l p = uncurryT2 (/) . getSum
                   . foldMap (\(x,y) -> Sum (T2 (f x y) 1))
  where
    f = testLearn t l p

newtype M m a = M { getM :: m a }
instance (Semigroup a, Applicative m) => Semigroup (M m a) where
    M x <> M y = M $ liftA2 (<>) x y
instance (Monoid a, Applicative m) => Monoid (M m a) where
    mappend = (<>)
    mempty = M (pure mempty)

testLearnStochAll
    :: (Learn a b l, NoState l, PrimMonad m, Foldable t)
    => Test b
    -> l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> t (a, b)
    -> m Double
testLearnStochAll t l g p = fmap (uncurryT2 (/) . getSum) . getM
                          . foldMap (\(x,y) -> M $ Sum . (`T2` 1) <$> f x y)
  where
    f = testLearnStoch t l g p

testLearnStochCov
    :: (Learn a b l, NoState l, PrimMonad m, Foldable t, Fractional b)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> t (a, b)
    -> m b
testLearnStochCov l g p = fmap (process . getSum) . getM . foldMap (M . go)
  where
    process (T3 (T2 x y) xy n) = xy / n - (x * y) / n / n
    go (x, y) = do
        r <- runLearnStochStateless_ l g p x
        pure (Sum $ T3 (T2 r y) (r * y) 1)

testLearnStochCorr
    :: (Learn a b l, NoState l, PrimMonad m, Foldable t, Floating b)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> t (a, b)
    -> m b
testLearnStochCorr l g p = fmap (process . getSum) . getM . foldMap (M . go)
  where
    process (T3 (T2 (T2 x x2) (T2 y y2)) xy n) = (xy / n - (x * y) / n / n)
            / sqrt ( x2 / n - (x / n)**2 )
            / sqrt ( y2 / n - (y / n)**2 )
    go (x, y) = do
        r  <- runLearnStochStateless_ l g p x
        pure (Sum $ T3 (T2 (T2 r (r**2)) (T2 y (y**2))) (r * y) 1)
