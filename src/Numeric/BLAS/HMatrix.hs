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
{-# LANGUAGE UndecidableInstances       #-}

module Numeric.BLAS.HMatrix (
    HM(..)
  , HM'
  ) where

import           Control.DeepSeq
import           Data.Finite.Internal
import           Data.Foldable
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
import qualified Numeric.LinearAlgebra        as LA

type family HM' (s :: [Nat]) = (h :: Type) | h -> s where
    HM' '[n]   = R n
    HM' '[m,n] = L m n

newtype HM :: [Nat] -> Type where
    HM  :: { getHM :: HM' b }
        -> HM b
  deriving (Generic)

type instance Element (HM s) = Double

instance BLAS HM where

    bkonst = \case
      SNat `SCons` SNil      -> HM . konst
      SNat `SCons` (SNat `SCons` SNil) -> HM . konst

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
      n@SNat `SCons` SNil -> \f -> HM . fromJust . create $
        LA.build (fromIntegral (fromSing n))
          (f . only . Finite . round)
      m@SNat `SCons` (n@SNat `SCons` SNil) -> \f -> HM . fromJust . create $
        LA.build (fromIntegral (fromSing m), fromIntegral (fromSing n))
          (\i j -> f (Finite (round i) :< Finite (round j) :< Ø))

    genA = \case
      n@SNat `SCons` SNil -> \f ->
        fmap (HM . vector) . traverse (f . only . Finite) $
          [0 .. fromSing n - 1]
      m@SNat `SCons` (n@SNat `SCons` SNil) -> \f ->
        fmap (HM . matrix) . traverse f $
          [ Finite i :< Finite j :< Ø | j <- [0 .. fromSing m - 1]
                                      , i <- [0 .. fromSing n - 1]
          ]

    tkonst = \case
      SNat `SCons` SNil      -> HM . konst
      SNat `SCons` (SNat `SCons` SNil) -> HM . konst

    tsum :: forall s. SingI s => HM s -> Double
    tsum = case sing @_ @s of
      SNat `SCons` SNil      -> LA.sumElements . extract . getHM
      SNat `SCons` (SNat `SCons` SNil) -> LA.sumElements . extract . getHM

    tmap :: forall s. SingI s => (Double -> Double) -> HM s -> HM s
    tmap = omap

    tzip
        :: forall s. SingI s
        => (Double -> Double -> Double)
        -> HM s -> HM s -> HM s
    tzip f (HM x) (HM y) = case sing @_ @s of
      SNat `SCons` SNil      -> HM $ zipWithVector f x y
      SNat `SCons` (SNat `SCons` SNil) -> HM $ matrix (zipWith f (concat . LA.toLists . extract $ x)
                                              (concat . LA.toLists . extract $ y)
                                   )

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
    tindex = case sing @_ @s of
      SNat `SCons` SNil -> \case
        i :< Ø -> \case
          HM x -> extract x `LA.atIndex` fromIntegral i
      SNat `SCons` (SNat `SCons` SNil) -> \case
        i :< j :< Ø -> \case
          HM x -> extract x `LA.atIndex` (fromIntegral i, fromIntegral j)

instance SingI s => MonoFunctor (HM s) where
    omap f (HM x) = case sing @_ @s of
      SNat `SCons` SNil      -> HM (dvmap f x)
      SNat `SCons` (SNat `SCons` SNil) -> HM (dmmap f x)

hmElems :: forall s. SingI s => HM s -> [Double]
hmElems = case sing @_ @s of
    SNat `SCons` SNil      -> LA.toList . extract . getHM
    SNat `SCons` (SNat `SCons` SNil) -> concat . LA.toLists . extract . getHM

instance SingI s => MonoFoldable (HM s) where
    ofoldMap f     = foldMap f . hmElems
    ofoldr f z     = foldr f z . hmElems
    ofoldl' f z    = foldl' f z . hmElems
    otoList        = hmElems
    oall f         = all f . hmElems
    oany f         = any f . hmElems
    onull          = (== 0) . olength
    olength        = case sing @_ @s of
      SNat `SCons` SNil      -> size . getHM
      SNat `SCons` (SNat `SCons` SNil) -> uncurry (*) . size . getHM
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

