{-# LANGUAGE FlexibleContexts                     #-}
{-# LANGUAGE PartialTypeSignatures                #-}
{-# LANGUAGE RankNTypes                           #-}
{-# LANGUAGE TypeApplications                     #-}
{-# LANGUAGE TypeFamilies                         #-}
{-# LANGUAGE ViewPatterns                         #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Backprop.Learn.Test (
  -- * Tests
    Test
  , maxIxTest, rmseTest, squaredErrorTest, crossEntropyTest
  -- * Run tests
  , testLearn, testLearnStoch, testLearnAll, testLearnStochAll
  ) where

import           Backprop.Learn.Model
import           Control.Applicative
import           Control.Monad.Primitive
import           Data.Function
import           Data.Semigroup
import           Data.Type.Combinator
import           GHC.TypeNats
import           Numeric.Backprop.Tuple
import qualified Numeric.LinearAlgebra        as HU
import qualified Numeric.LinearAlgebra.Static as H
import qualified System.Random.MWC            as MWC

type Test o = o -> o -> Double

maxIxTest :: KnownNat n => Test (H.R n)
maxIxTest x y
    | match x y = 1
    | otherwise = 0
  where
    match = (==) `on` (HU.maxIndex . H.extract)

rmseTest :: KnownNat n => Test (H.R n)
rmseTest x y = H.norm_2 (x - y)

squaredErrorTest :: KnownNat n => Test (H.R n)
squaredErrorTest x y = e `H.dot` e
  where
    e = x - y

crossEntropyTest :: KnownNat n => Test (H.R n)
crossEntropyTest targ res = -(log res H.<.> targ)

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
