{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

module Numeric.BLAS.FVector where
-- module Numeric.BLAS.FVector (
--   ) where

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
import           Numeric.Tensor
import qualified Data.Vector.Sized        as SV
import qualified Data.Vector.Unboxed      as VU

newtype FV :: [Nat] -> Type where
    FV  :: { getFV :: VU.Vector Double
           }
        -> FV b
  deriving (Generic, Show)

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
              in  VU.concat
                . fmap (go ss pms)
                . chunksOf innerSize
                . VU.slice dropper taker
        chunksOf :: Int -> VU.Vector Double -> [VU.Vector Double]
        chunksOf l = unfoldr $ \xs -> do
          if VU.length xs >= l
            then Just (VU.splitAt l xs)
            else Nothing

    tindex i (FV xs) = xs VU.! fromIntegral (getFinite (reIndex i))

    treshape _ (FV xs) = FV xs
    tload _ = FV . VU.convert . SV.fromSized
    textract
        :: forall s. SingI s
        => FV s
        -> SV.Vector (Product s) Double
    textract = withKnownNat (sProduct (sing @_ @s)) $
      fromJust . SV.toSized . VU.convert . getFV

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
      Ø                     -> (0, 0)
    SNat `SCons` ss -> \case
      (i :: Finite n) :< is ->
        let (j, jSize) = unsafeReIndex ss is
            iSize = jSize * (fromSing (SNat @n))
        in  (j + jSize * getFinite i, iSize)

-- unsafeReIndex
--     :: Integer
--     -> Sing ns
--     -> Prod Finite ns
-- unsafeReIndex i = \case
--     SNil -> Ø
--     s `SCons` ss ->
--       let (j,k) = i `divMod` fromSing s
--       in  Finite j :< unsafeReIndex k ss


