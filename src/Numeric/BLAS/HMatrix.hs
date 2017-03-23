{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE UndecidableInstances #-}

module Numeric.BLAS.HMatrix (
    HM(..)
  , HM'
  ) where

import           Data.Finite.Internal
import           Data.Foldable
import           Data.Kind
import           Data.Maybe
import           Data.MonoTraversable
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Numeric.BLAS hiding          (outer)
import           Numeric.LinearAlgebra.Static
import           Numeric.Tensor
import qualified Numeric.LinearAlgebra        as LA

type family HM' (s :: BShape) :: Type where
    HM' ('BV n  ) = R n
    HM' ('BM m n) = L m n

newtype HM :: BShape -> Type where
    HM  :: { getHM :: HM' b }
        -> HM b

type instance Element (HM s) = Double

instance BLAS HM where
    type Scalar HM = Double

    bkonst = \case
      SBV SNat      -> HM . konst
      SBM SNat SNat -> HM . konst

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
    type IndexT HM = BIndex
    type ElemT  HM = Double

    gen = \case
      SBV n@SNat -> \f -> HM . fromJust . create $
        LA.build (fromIntegral (fromSing n))
          (f . BVIx . Finite . round)
      SBM m@SNat n@SNat -> \f -> HM . fromJust . create $
        LA.build (fromIntegral (fromSing m), fromIntegral (fromSing n))
          (\i j -> f (BMIx (Finite (round i)) (Finite (round j))))

    genA = \case
      SBV n@SNat -> \f ->
        fmap (HM . vector) . traverse (f . BVIx . Finite) $
          [0 .. fromSing n - 1]
      SBM m@SNat n@SNat -> \f ->
        fmap (HM . matrix) . traverse f $
          [ BMIx (Finite i) (Finite j) | j <- [0 .. fromSing m - 1]
                                       , i <- [0 .. fromSing n - 1]
          ]

    tkonst = \case
      SBV SNat      -> HM . konst
      SBM SNat SNat -> HM . konst

    tsum :: forall s. SingI s => HM s -> Double
    tsum = case sing @_ @s of
      SBV SNat      -> LA.sumElements . extract . getHM
      SBM SNat SNat -> LA.sumElements . extract . getHM

    tmap :: forall s. SingI s => (Double -> Double) -> HM s -> HM s
    tmap = omap

    tzip
        :: forall s. SingI s
        => (Double -> Double -> Double)
        -> HM s -> HM s -> HM s
    tzip f (HM x) (HM y) = case sing @_ @s of
      SBV SNat      -> HM $ zipWithVector f x y
      SBM SNat SNat -> HM $ matrix (zipWith f (concat . LA.toLists . extract $ x)
                                              (concat . LA.toLists . extract $ y)
                                   )

    tsize
        :: forall s. SingI s
        => HM s
        -> Int
    tsize _ = fromIntegral $ bshapeSize (fromSing (sing @_ @s))

    tindex
        :: forall s. SingI s
        => BIndex s
        -> HM s
        -> Double
    tindex = case sing @_ @s of
      SBV SNat -> \case
        BVIx i -> \case
          HM x -> extract x `LA.atIndex` fromIntegral i
      SBM SNat SNat -> \case
        BMIx i j -> \case
          HM x -> extract x `LA.atIndex` (fromIntegral i, fromIntegral j)


instance SingI s => MonoFunctor (HM s) where
    omap f (HM x) = case sing @_ @s of
      SBV SNat      -> HM (dvmap f x)
      SBM SNat SNat -> HM (dmmap f x)

hmElems :: forall s. SingI s => HM s -> [Double]
hmElems = case sing @_ @s of
    SBV SNat      -> LA.toList . extract . getHM
    SBM SNat SNat -> concat . LA.toLists . extract . getHM

instance SingI s => MonoFoldable (HM s) where
    ofoldMap f     = foldMap f . hmElems
    ofoldr f z     = foldr f z . hmElems
    ofoldl' f z    = foldl' f z . hmElems
    otoList        = hmElems
    oall f         = all f . hmElems
    oany f         = any f . hmElems
    onull          = (== 0) . olength
    olength        = case sing @_ @s of
      SBV SNat      -> size . getHM
      SBM SNat SNat -> uncurry (*) . size . getHM
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

instance Num (HM' s) => Num (HM s) where
    HM x + HM y = HM (x + y)
    HM x - HM y = HM (x - y)
    HM x * HM y = HM (x * y)
    negate (HM x) = HM (negate x)
    signum (HM x) = HM (signum x)
    abs    (HM x) = HM (abs    x)
    fromInteger x = HM (fromInteger x)
