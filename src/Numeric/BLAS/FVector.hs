{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Numeric.BLAS.FVector (
    FV(..)
  ) where

import           Control.DeepSeq
import           Data.Finite
import           Data.Finite.Internal
import           Data.Kind
import           Data.List
import           Data.Maybe
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           Data.Type.Combinator
import           Data.Type.Product
import           Data.Type.Vector
import           GHC.Generics             (Generic)
import           GHC.TypeLits
import           Lens.Micro
import           Numeric.BLAS
import           Numeric.Tensor
import qualified Data.Vector.Sized        as SV
import qualified Data.Vector.Unboxed      as VU

newtype FV :: [Nat] -> Type where
    FV  :: { getFV :: VU.Vector Double
           }
        -> FV b
  deriving (Generic)

instance Tensor FV where
    type Scalar FV = Double

    genA s f = fmap (FV . VU.fromList) . traverse f $ range s
    gen s f = FV . VU.fromList . fmap f $ range s
    tkonst s = FV . VU.replicate (fromIntegral (product (fromSing s)))
    tsum = VU.sum . getFV
    tmap f = FV . VU.map f . getFV
    tzip f (FV xs) (FV ys) = FV (VU.zipWith f xs ys)
    tzipN
        :: forall s n. SingI s
        => (Vec n Double -> Double)
        -> VecT n FV s
        -> FV s
    tzipN f xs = FV $ VU.generate (fromIntegral len) $ \i ->
                   (f (vmap (I . (VU.! i)) xs'))
      where
        len = product (fromSing (sing @_ @s))
        xs' = vmap getFV xs


    tslice p0 = FV . go sing p0 . getFV
      where
        go :: Sing ns -> ProdMap Slice ns ms -> VU.Vector Double -> VU.Vector Double
        go = \case
          SNil -> \case
            PMZ -> id
          SNat `SCons` ss -> \case
            PMS (Slice sL sC _) pms ->
              let -- some wasted work here in re-computing the product,
                  -- but premature optimization blah blah
                  innerSize = fromIntegral (product (fromSing ss))
                  dropper   = innerSize * fromIntegral (fromSing sL)
                  taker     = innerSize * fromIntegral (fromSing sC)
              in  over (chunks innerSize) (go ss pms)
                . VU.slice dropper taker

    tindex i (FV xs) = xs VU.! fromIntegral (getFinite (reIndex i))

    treshape _ (FV xs) = FV xs
    tload _ = FV . VU.convert . SV.fromSized
    textract
        :: forall s. SingI s
        => FV s
        -> SV.Vector (Product s) Double
    textract = withKnownNat (sProduct (sing @_ @s)) $
      fromJust . SV.toSized . VU.convert . getFV

instance BLAS FV where

    iamax
        :: forall n. KnownNat n
        => FV '[n + 1]
        -> Finite (n + 1)
    iamax = withKnownNat (SNat @n %:+ SNat @1) $
        Finite . fromIntegral . VU.maxIndex . VU.map abs . getFV

    gemv
        :: forall m n. (KnownNat m, KnownNat n)
        => Double
        -> FV '[m, n]
        -> FV '[n]
        -> Maybe (Double, FV '[m])
        -> FV '[m]
    gemv α (FV a) (FV x) b =
          FV
        . maybe id (\(β, FV ys) -> VU.zipWith (\y z -> β * y + z) ys) b
        . over (chunkDown innerSize) (\r -> α * VU.sum (VU.zipWith (*) r x))
        $ a
      where
        innerSize = fromIntegral $ natVal (Proxy @n)

    ger α (FV xs) (FV ys) b =
          FV
        . maybe id (\(FV zs) -> VU.zipWith (+) zs) b
        . VU.concatMap (\x -> VU.map ((α * x) *) ys)
        $ xs

    gemm
        :: forall m o n. (KnownNat m, KnownNat o, KnownNat n)
        => Double
        -> FV '[m, o]
        -> FV '[o, n]
        -> Maybe (Double, FV '[m, n])
        -> FV '[m, n]
    gemm α (FV as) bs cs =
          FV
        . maybe id (uncurry f) cs
        . over (chunks innerSize) muller
        $ as
      where
        innerSize = fromIntegral $ natVal (Proxy @o)
        muller r =
            over (chunkDown innerSize) (\c -> α * VU.sum (VU.zipWith (*) r c))
          . getFV
          $ transp bs
        f β (FV cs') = VU.zipWith (\c b -> β * c + b) cs'

range :: Sing ns -> [Prod Finite ns]
range = \case
    SNil            -> [Ø]
    SNat `SCons` ss -> (:<) <$> finites <*> range ss

reIndex
    :: SingI ns
    => Prod Finite ns
    -> Finite (Product ns)
reIndex = Finite . fst . unsafeReIndex sing

unsafeReIndex
    :: Sing ns
    -> Prod Finite ns
    -> (Integer, Integer)
unsafeReIndex = \case
    SNil -> \case
      Ø                     -> (0, 1)
    SNat `SCons` ss -> \case
      (i :: Finite n) :< is ->
        let (j, jSize) = unsafeReIndex ss is
            iSize = jSize * (fromSing (SNat @n))
        in  (j + jSize * getFinite i, iSize)

chunks
    :: (VU.Unbox a, VU.Unbox b)
    => Int
    -> Traversal (VU.Vector a) (VU.Vector b) (VU.Vector a) (VU.Vector b)
chunks n f = fmap VU.concat . traverse f . unfoldr u
  where
    u xs | VU.length xs >= n = Just (VU.splitAt n xs)
         | otherwise         = Nothing

chunkDown
    :: (VU.Unbox a, VU.Unbox b)
    => Int
    -> Traversal (VU.Vector a) (VU.Vector b) (VU.Vector a) b
chunkDown n f = fmap VU.fromList . traverse f . unfoldr u
  where
    u xs | VU.length xs >= n = Just (VU.splitAt n xs)
         | otherwise         = Nothing

deriving instance NFData (FV s)
deriving instance Show (FV s)
-- deriving instance Num (FV s)
-- deriving instance Fractional (FV s)
-- deriving instance Floating (FV s)

