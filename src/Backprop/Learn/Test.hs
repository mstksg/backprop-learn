{-# LANGUAGE ApplicativeDo                   #-}
{-# LANGUAGE DataKinds                       #-}
{-# LANGUAGE FlexibleContexts                #-}
{-# LANGUAGE PartialTypeSignatures           #-}
{-# LANGUAGE RankNTypes                      #-}
{-# LANGUAGE ScopedTypeVariables             #-}
{-# LANGUAGE TypeApplications                #-}
{-# LANGUAGE TypeFamilies                    #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Backprop.Learn.Test (
  -- * Tests
    Test
  , maxIxTest, rmseTest
  , squaredErrorTest, absErrorTest, totalSquaredErrorTest, squaredErrorTestV
  , crossEntropyTest, crossEntropyTest1
  , boolTest
  -- ** Manipulate tests
  , lossTest, lmapTest
  -- * Run tests
  , testModel, testModelStoch, testModelAll, testModelStochAll
  -- ** Correlation tests
  , testModelCov, testModelCorr
  , testModelStochCov, testModelStochCorr
  ) where

import           Backprop.Learn.Loss
import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Function
import           Data.Functor.Identity
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

boolTest :: forall a. RealFrac a => Test a
boolTest x y
    | ri x == ri y = 1
    | otherwise    = 0
  where
    ri :: a -> Int
    ri = round

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

crossEntropyTest1 :: Test Double
crossEntropyTest1 targ res = -(log res * targ + log (1 - res) * (1 - targ))

lmapTest
    :: (a -> b)
    -> Test b
    -> Test a
lmapTest f t x y = t (f x) (f y)

testModel
    :: Test b
    -> Model p 'Nothing a b
    -> PMaybe Identity p
    -> a
    -> b
    -> Double
testModel t f mp x y = t y $ runModelStateless f mp x

testModelStoch
    :: PrimMonad m
    => Test b
    -> Model p 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> PMaybe Identity p
    -> a
    -> b
    -> m Double
testModelStoch t f g mp x y = t y <$> runModelStochStateless f g mp x

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

testModelCov
    :: (Foldable t, Fractional b)
    => Model p 'Nothing a b
    -> PMaybe Identity p
    -> t (a, b)
    -> b
testModelCov f p = L.fold $ (lmap . first) (runModelStateless f p) cov

testModelCorr
    :: (Foldable t, Floating b)
    => Model p 'Nothing a b
    -> PMaybe Identity p
    -> t (a, b)
    -> b
testModelCorr f p = L.fold $ (lmap . first) (runModelStateless f p) corr

testModelAll
    :: Foldable t
    => Test b
    -> Model p 'Nothing a b
    -> PMaybe Identity p
    -> t (a, b)
    -> Double
testModelAll t f p = L.fold $ lmap (uncurry (testModel t f p)) L.mean

-- newtype M m a = M { getM :: m a }
-- instance (Semigroup a, Applicative m) => Semigroup (M m a) where
--     M x <> M y = M $ liftA2 (<>) x y
-- instance (Monoid a, Applicative m) => Monoid (M m a) where
--     mappend = (<>)
--     mempty = M (pure mempty)

testModelStochAll
    :: (Foldable t, PrimMonad m)
    => Test b
    -> Model p 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> PMaybe Identity p
    -> t (a, b)
    -> m Double
testModelStochAll t f g p = L.foldM $ L.premapM (uncurry (testModelStoch t f g p))
                                      (L.generalize L.mean)

testModelStochCov
    :: (Foldable t, PrimMonad m, Fractional b)
    => Model p 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> PMaybe Identity p
    -> t (a, b)
    -> m b
testModelStochCov f g p = L.foldM $ (L.premapM . flip bitraverse pure)
                                      (runModelStochStateless f g p)
                                      (L.generalize cov)

testModelStochCorr
    :: (Foldable t, PrimMonad m, Floating b)
    => Model p 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> PMaybe Identity p
    -> t (a, b)
    -> m b
testModelStochCorr f g p = L.foldM $ (L.premapM . flip bitraverse pure)
                                       (runModelStochStateless f g p)
                                       (L.generalize corr)
