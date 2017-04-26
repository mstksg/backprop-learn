{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module Numeric.BLAS.NVector (
    NV(..)
  , NV'
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Kind
import           Data.Maybe
import           Data.Monoid                (Endo(..))
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           Data.Type.Product
import           GHC.Generics               (Generic)
import           Numeric.BLAS
import           Numeric.Tensor
import qualified Data.Vector                as UV
import qualified Data.Vector.Sized          as V
import qualified Data.Vector.Storable       as UVS
import qualified Data.Vector.Storable.Sized as VS


type family NV' (s :: [Nat]) = (h :: Type) | h -> s where
    NV' '[]       = Double
    NV' (n ': ns) = V.Vector n (NV' ns)

newtype NV :: [Nat] -> Type where
    NV  :: { getNV :: NV' b }
        -> NV b
  deriving (Generic)

genNV :: Sing ns -> (Prod Finite ns -> Double) -> NV' ns
genNV = \case
    SNil -> \f -> f Ø
    SNat `SCons` ss -> \f -> V.generate_ $ \i ->
      genNV ss (f . (i :<))

genNVA
    :: Applicative f
    => Sing ns
    -> (Prod Finite ns -> f Double)
    -> f (NV' ns)
genNVA = \case
    SNil -> \f -> f Ø
    SNat `SCons` ss -> \f -> sequenceA . V.generate_ $ \i ->
      genNVA ss (f . (i :<))

sumNV
    :: Sing ns
    -> NV' ns
    -> Double
sumNV = \case
    SNil -> id
    _ `SCons` ss -> V.sum . fmap (sumNV ss)

mapNV
    :: Sing ns
    -> (Double -> Double)
    -> NV' ns
    -> NV' ns
mapNV = \case
    SNil -> id
    _ `SCons` ss -> \f -> fmap (mapNV ss f)

zipNV
    :: Sing ns
    -> (Double -> Double -> Double)
    -> NV' ns
    -> NV' ns
    -> NV' ns
zipNV = \case
    SNil -> id
    _ `SCons` ss -> \f -> V.zipWith (zipNV ss f)

indexNV
    :: Sing ns
    -> Prod Finite ns
    -> NV' ns
    -> Double
indexNV = \case
    SNil -> \case
      Ø -> id
    SNat `SCons` ss -> \case
      i :< is -> indexNV ss is . flip V.index i

loadNV
    :: Sing ns
    -> V.Vector (Product ns) Double
    -> NV' ns
loadNV = \case
    SNil -> V.head
    sn@SNat `SCons` ss -> case sProduct ss of
      sp@SNat -> fromJust
               . V.fromList
               . evalState (replicateM (fromInteger (fromSing sn)) (
                              loadNV ss . fromJust . V.toSized
                                <$> state (UV.splitAt (fromInteger (fromSing sp)))
                           ))
               . V.fromSized

nvElems
    :: Sing ns
    -> NV' ns
    -> [Double]
nvElems s n = appEndo (go s n) []
  where
    go :: Sing ms -> NV' ms -> Endo [Double]
    go = \case
      SNil -> \x   -> Endo (x:)
      _ `SCons` ss -> foldMap (go ss)

sliceNV
    :: ProdMap Slice ns ms
    -> NV' ns
    -> NV' ms
sliceNV = \case
    PMZ -> id
    PMS (Slice sL sC@SNat _) pms ->
      let l = fromIntegral $ fromSing sL
          c = fromIntegral $ fromSing sC
      in  fmap (sliceNV pms)
            . fromJust . V.toSized
            . UV.take c
            . UV.drop l
            . V.fromSized

instance Tensor NV where
    type Scalar NV = Double

    gen s  = NV . genNV s
    genA s = fmap NV . genNVA s
    tsum   = sumNV sing . getNV
    tmap f = NV . mapNV sing f . getNV
    tzip f xs ys = NV $ zipNV sing f (getNV xs) (getNV ys)

    tsize :: forall s. SingI s => NV s -> Int
    tsize _ = fromIntegral $ product (fromSing (sing @_ @s))

    tindex i = indexNV sing i . getNV

    tload s = NV . loadNV s
    textract = withKnownNat (sProduct ss) $
        fromJust . V.fromList . nvElems ss . getNV
      where
        ss = sing

    tslice p = NV . sliceNV p . getNV

instance BLAS NV where
    transp = NV . sequenceA  . getNV
    scal α = NV . fmap (α *) . getNV
    axpy α (NV xs) (NV ys) = NV $ liftA2 (\x y -> α * x + y) xs ys
    dot (NV xs) (NV ys) = V.sum $ V.zipWith (*) xs ys
    norm2 = V.sum . fmap (**2) . getNV
    asum  = V.sum . fmap abs . getNV
    iamax = fromIntegral . UV.maxIndex . fmap abs . V.fromSized . getNV

    gemv α (NV a) (NV xs) b = maybe id (uncurry axpy) b
                            . NV
                            . fmap (V.sum . V.zipWith (\x -> (* (x * α))) xs)
                            $ a

    ger α (NV xs) (NV ys) a = NV . addA $ fmap (\x -> fmap (* (x * α)) ys) xs
      where
        addA = case a of
          Nothing      -> id
          Just (NV a') -> (V.zipWith . V.zipWith) (+) a'

    gemm α (NV ass) (NV bss) c = NV . addC $
        fmap (sumVs . V.zipWith (\bs a -> fmap (* (α * a)) bs) bss) ass
      where
        sumVs = V.foldl' (V.zipWith (+)) (V.generate (\_ -> 0))
        addC = case c of
          Nothing -> id
          Just (β, NV css) -> (V.zipWith . V.zipWith) (\c' -> (+ (β * c'))) css

