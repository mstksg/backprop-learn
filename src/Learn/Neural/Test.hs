{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Learn.Neural.Test (
    TestFunc
  , maxTest
  , rmseTest
  , testNet
  , testNetList
  ) where

import           GHC.TypeLits
import           Learn.Neural.Layer
import           Learn.Neural.Network
import           Numeric.BLASTensor
import qualified Control.Foldl        as F

type TestFunc o = forall b. (BLASTensor b, Num (b o)) => b o -> b o -> Double

maxTest :: KnownNat n => TestFunc (BV n)
maxTest x y | iamax x == iamax y = 1
            | otherwise          = 0

rmseTest :: KnownNat n => TestFunc (BV n)
rmseTest x y = realToFrac $ e `dot` e
  where
    e = axpy (-1) x y

testNet
    :: (BLASTensor b, Num (b i), Num (b o))
    => TestFunc o
    -> SomeNet 'FeedForward b i o
    -> b i
    -> b o
    -> Double
testNet tf = \case
    SomeNet _ n -> \x t ->
      let y = runNetworkPure n x
      in  tf y t

testNetList
    :: (BLASTensor b, Num (b i), Num (b o))
    => TestFunc o
    -> SomeNet 'FeedForward b i o
    -> [(b i, b o)]
    -> Double
testNetList tf n = F.fold F.mean . fmap (uncurry (testNet tf n))
