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
{-# LANGUAGE ViewPatterns               #-}

module Numeric.BLAS.HMatrix (
    HM(..)
  , HM'
  ) where

import           Control.Applicative
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
import qualified Data.Vector                  as UV
import qualified Data.Vector.Sized            as V
import qualified Data.Vector.Storable         as UVS
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

    tkonst s = HM . hkonst s

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
    tzip f (HM x0) (HM y0) = HM $ hzip f sing x0 y0

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

    tconv
        :: forall m s. ()
        => DoubleProd Sing m s
        -> HM m
        -> HM s
        -> HM s
    tconv dp0 (HM m0) (HM x0) = HM $ go dp0 m0 x0
      where
        go  :: forall ms ns. ()
            => DoubleProd Sing ms ns
            -> HM' ms
            -> HM' ns
            -> HM' ns
        go = \case
          DPZ -> (*)
          DPS sm@SNat sn@SNat DPZ -> \m x -> fromJust . create $
            let c = LA.conv (extract m) (extract x)
                left = fromInteger (fromSing sm) `div` 2
            in  UVS.slice left (fromInteger (fromSing sn)) c
          DPS smx@SNat snx@SNat (DPS smy@SNat sny@SNat DPZ) -> \m x -> fromJust . create $
            let c = LA.conv2 (extract m) (extract x)
                left = fromInteger (fromSing smx) `div` 2
                top  = fromInteger (fromSing smy) `div` 2
            in  LA.subMatrix (left, top) (fromInteger (fromSing snx), fromInteger (fromSing sny)) c
          DPS (SNat :: Sing m0) (SNat :: Sing n0) dps@(DPS _ _ (DPS _ _ _) :: DoubleProd Sing ms0 ns0) ->
                    \(ms :: V.Vector m0 (HM' ms0)) (xs :: V.Vector n0 (HM' ns0)) ->
            let s   :: Sing ns0
                s   = prodSing $ secondDP dps
                cl :: V.Vector n0 (V.Vector m0 (HM' ns0))
                cl = im2col (hkonst s 0) xs
            in  fmap (hsum s . V.zipWith (go dps) ms) cl

im2col
    :: forall m n a. (KnownNat m, KnownNat n)
    => a
    -> V.Vector n a
    -> V.Vector n (V.Vector m a)
im2col pad (V.fromSized->v) = V.generate $ \i ->
      fromMaybe (error "what") . V.toSized $ UV.slice i m padded
  where
    padded = UV.concat [UV.replicate left pad, v, UV.replicate right pad]
    m :: Int
    m  = fromIntegral $ natVal (Proxy @m)
    left  = m `div` 2
    right = m - left

hadd :: Sing s -> HM' s -> HM' s -> HM' s
hadd = \case
    SNil -> (+)
    SNat `SCons` SNil                        -> (+)
    SNat `SCons` (SNat `SCons` SNil)         -> (+)
    SNat `SCons` s@(_ `SCons` (_ `SCons` _)) -> liftA2 (hadd s)

hsum :: Foldable f => Sing s -> f (HM' s) -> HM' s
hsum s = foldl' (hadd s) (hkonst s 0)

hkonst :: Sing s -> Double -> HM' s
hkonst = \case
    SNil                                     -> id
    SNat `SCons` SNil                        -> konst
    SNat `SCons` (SNat `SCons` SNil)         -> konst
    SNat `SCons` s@(_ `SCons` (_ `SCons` _)) -> pure . hkonst s

hzip
    :: (Double -> Double -> Double)
    -> Sing s
    -> HM' s
    -> HM' s
    -> HM' s
hzip f = go
  where
    go :: Sing t -> HM' t -> HM' t -> HM' t
    go = \case
      SNil                             -> f
      SNat `SCons` SNil                -> zipWithVector f
      SNat `SCons` (SNat `SCons` SNil) ->
        (\xs ys -> matrix (zipWith f xs ys))
           `on` (concat . LA.toLists . extract)
      SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) ->
         V.zipWith (go ns)

firstDP
    :: DoubleProd f as bs
    -> Prod f as
firstDP = \case
    DPZ        -> Ø
    DPS x _ xs -> x :< firstDP xs

secondDP
    :: DoubleProd f as bs
    -> Prod f bs
secondDP = \case
    DPZ        -> Ø
    DPS _ x xs -> x :< secondDP xs

prodSing
    :: Prod Sing as
    -> Sing as
prodSing = \case
    Ø       -> SNil
    x :< xs -> x `SCons` prodSing xs

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

deriving instance NFData (HM' s)     => NFData (HM s)
deriving instance Show (HM' s)       => Show (HM s)
deriving instance Num (HM' s)        => Num (HM s)
deriving instance Fractional (HM' s) => Fractional (HM s)

