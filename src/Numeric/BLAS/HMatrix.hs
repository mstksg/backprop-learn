{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Numeric.BLAS.HMatrix (
    HM(..)
  , HM'
  ) where

import           Control.DeepSeq
import           Data.Finite.Internal
import           Data.Foldable
import           Data.Function
import           Data.Kind
import           Data.Maybe
import           Data.MonoTraversable
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           Data.Type.Product
import           GHC.Generics                 (Generic)
import           Numeric.BLAS hiding          (outer)
import           Numeric.LinearAlgebra.Static
import qualified Data.Vector.Sized            as V
import qualified Numeric.LinearAlgebra        as LA

type family HM' (s :: [Nat]) = (h :: Type) | h -> s where
    HM' '[]            = Double
    HM' '[n]           = R n
    HM' '[m,n]         = L m n
    HM' (n ': m ': ms) = V.Vector n (HM' (m ': ms))

newtype HM :: [Nat] -> Type where
    HM  :: { getHM :: HM' b }
        -> HM b
  deriving (Generic)

type instance Element (HM s) = Double

instance BLAS HM where

    transp (HM x) = HM (tr x)

    scal α (HM x)        = HM (konst α * x)
    axpy α (HM x) (HM y) = HM (konst α * x + y)
    dot    (HM x) (HM y) = x <.> y
    norm2  (HM x)        = norm_2 x
    asum   (HM x)        = norm_1 x
    iamax  (HM x)        = Finite . fromIntegral
                         . LA.maxIndex . extract
                         $ abs x

    gemv α (HM a) (HM x) = \case
        Just (β, HM y) -> HM (konst α * (a #> x) + konst β * y)
        Nothing        -> HM (konst α * (a #> x))
    ger  α (HM x) (HM y) = \case
        Just (HM a) -> HM (konst α * outer x y + a)
        Nothing     -> HM (konst α * outer x y)
    syr  α (HM x) (HM a)          = HM (konst α * outer x x + a)
    gemm α (HM a) (HM b) = \case
        Just (β, HM c) -> HM (konst α * (a <> b) + konst β * c)
        Nothing        -> HM (konst α * (a <> b))
    syrk α (HM a) β (HM c)        = HM (konst α * (a <> tr a) + konst β * c)

instance Tensor HM where
    type Scalar  HM = Double

    gen = \case
      SNil -> \f -> HM $ f Ø
      n@SNat `SCons` SNil -> \f -> HM . fromJust . create $
        LA.build (fromIntegral (fromSing n))
          (f . only . Finite . round)
      m@SNat `SCons` (n@SNat `SCons` SNil) -> \f -> HM . fromJust . create $
        LA.build (fromIntegral (fromSing m), fromIntegral (fromSing n))
          (\i j -> f (Finite (round i) :< Finite (round j) :< Ø))
      SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> \f -> HM $
        V.generate_ $ \i -> getHM $ gen ns (\js -> f (i :< js))

    genA = \case
      SNil -> \f -> HM <$> f Ø
      n@SNat `SCons` SNil -> \f ->
        fmap (HM . vector) . traverse (f . only . Finite) $
          [0 .. fromSing n - 1]
      m@SNat `SCons` (n@SNat `SCons` SNil) -> \f ->
        fmap (HM . matrix) . traverse f $
          [ Finite i :< Finite j :< Ø | j <- [0 .. fromSing m - 1]
                                      , i <- [0 .. fromSing n - 1]
          ]
      SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> \f -> fmap HM $
        sequenceA . V.generate_ $ \i -> getHM <$> genA ns (\js -> f (i :< js))

    tkonst = \case
      SNil                                      -> HM
      SNat `SCons` SNil                         -> HM . konst
      SNat `SCons` (SNat `SCons` SNil)          -> HM . konst
      SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> HM . pure . getHM . tkonst ns

    tsum :: forall s. SingI s => HM s -> Double
    tsum = go sing . getHM
      where
        go :: Sing ns -> HM' ns -> Double
        go = \case
          SNil                                      -> id
          SNat `SCons` SNil                         -> LA.sumElements . extract
          SNat `SCons` (SNat `SCons` SNil)          -> LA.sumElements . extract
          SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> sum . fmap (go ns)

    tmap :: forall s. SingI s => (Double -> Double) -> HM s -> HM s
    tmap = omap

    tzip
        :: forall s. SingI s
        => (Double -> Double -> Double)
        -> HM s -> HM s -> HM s
    tzip f (HM x0) (HM y0) = HM $ go sing x0 y0
      where
        go :: Sing ns -> HM' ns -> HM' ns -> HM' ns
        go = \case
          SNil                             -> f
          SNat `SCons` SNil                -> zipWithVector f
          SNat `SCons` (SNat `SCons` SNil) ->
            (\xs ys -> matrix (zipWith f xs ys))
               `on` (concat . LA.toLists . extract)
          SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) ->
             V.zipWith (go ns)

    tsize
        :: forall s. SingI s
        => HM s
        -> Int
    tsize _ = fromIntegral $ product (fromSing (sing @_ @s))

    tindex
        :: forall s. SingI s
        => Prod Finite s
        -> HM s
        -> Double
    tindex ix0 = go sing ix0 . getHM
      where
        go :: Sing ns -> Prod Finite ns -> HM' ns -> Double
        go = \case
          SNil -> \case
            Ø -> id
          SNat `SCons` SNil -> \case
            i :< Ø -> (`LA.atIndex` fromIntegral i) . extract
          SNat `SCons` (SNat `SCons` SNil) -> \case
            i :< j :< Ø -> (`LA.atIndex` (fromIntegral i, fromIntegral j)) . extract
          SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> \case
            i :< js -> go ns js . (`V.index` i)
              
instance SingI s => MonoFunctor (HM s) where
    omap f = HM . go sing . getHM
      where
        go :: Sing ns -> HM' ns -> HM' ns
        go = \case
          SNil                                      -> f
          SNat `SCons` SNil                         -> dvmap f
          SNat `SCons` (SNat `SCons` SNil)          -> dmmap f
          SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> fmap (go ns)

hmElems :: forall s. SingI s => HM s -> [Double]
hmElems = go sing . getHM
  where
    go :: Sing ns -> HM' ns -> [Double]
    go = \case
      SNil                                      -> (:[])
      SNat `SCons` SNil                         -> LA.toList . extract
      SNat `SCons` (SNat `SCons` SNil)          -> concat . LA.toLists . extract
      SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> foldMap (go ns)

instance SingI s => MonoFoldable (HM s) where
    ofoldMap f     = foldMap f . hmElems
    ofoldr f z     = foldr f z . hmElems
    ofoldl' f z    = foldl' f z . hmElems
    otoList        = hmElems
    oall f         = all f . hmElems
    oany f         = any f . hmElems
    onull          = (== 0) . olength
    olength _      = fromIntegral (product (fromSing (sing @_ @s)))
    olength64      = fromIntegral . olength
    ocompareLength = ocompareLength . hmElems
    otraverse_ f   = traverse_ f . hmElems
    ofor_ x        = for_ (hmElems x)
    omapM_ f       = traverse_ f . hmElems
    oforM_ x       = for_ (hmElems x)
    ofoldlM f x    = foldlM f x . hmElems
    ofoldMap1Ex f  = ofoldMap1Ex f . hmElems
    ofoldr1Ex f    = ofoldr1Ex f . hmElems
    ofoldl1Ex' f   = ofoldl1Ex' f . hmElems
    headEx         = headEx . hmElems
    lastEx         = lastEx . hmElems
    maximumByEx f  = maximumByEx f . hmElems
    minimumByEx f  = minimumByEx f . hmElems

deriving instance NFData (HM' s) => NFData (HM s)
deriving instance Show (HM' s) => Show (HM s)
deriving instance Num (HM' s) => Num (HM s)
deriving instance Fractional (HM' s) => Fractional (HM s)

