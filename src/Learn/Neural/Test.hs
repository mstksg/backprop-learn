{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Learn.Neural.Test (
    TestFunc
  , maxTest
  , rmseTest
  , squaredErrorTest
  , crossEntropyTest
  , testNet
  , testNetList
  ) where

import           Data.Proxy
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Learn.Neural.Network
import           Numeric.BLAS
import qualified Control.Foldl        as F

type TestFunc o = forall b. (BLAS b, Num (b o)) => b o -> b o -> Double

maxTest :: KnownNat n => TestFunc '[n + 1]
maxTest x y | iamax x == iamax y = 1
            | otherwise          = 0

rmseTest :: forall n. KnownNat n => TestFunc '[n]
rmseTest x y = sqrt $ realToFrac (e `dot` e) / fromIntegral (natVal (Proxy @n))
  where
    e = axpy (-1) x y

squaredErrorTest :: KnownNat n => TestFunc '[n]
squaredErrorTest x y = realToFrac $ e `dot` e
  where
    e = axpy (-1) x y

crossEntropyTest :: KnownNat n => TestFunc '[n]
crossEntropyTest r t = negate $ realToFrac (tmap log r `dot` t)

testNet
    :: (BLAS b, Num (b i), Num (b o))
    => TestFunc o
    -> SomeNet 'FeedForward b i o
    -> b i
    -> b o
    -> Double
testNet tf = \case
    SomeNet _ n -> \x t ->
      let y = runNetPure n x
      in  tf y t

testNetList
    :: (BLAS b, Num (b i), Num (b o))
    => TestFunc o
    -> SomeNet 'FeedForward b i o
    -> [(b i, b o)]
    -> Double
testNetList tf n = F.fold F.mean . fmap (uncurry (testNet tf n))
