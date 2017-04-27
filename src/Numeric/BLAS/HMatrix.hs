{-# LANGUAGE AllowAmbiguousTypes        #-}
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
  , flatten
  , unflatten
  ) where

import           Control.Applicative
import           Control.DeepSeq
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Finite.Internal
import           Data.Foldable
import           Data.Function
import           Data.Kind
import           Data.Maybe
import           Data.MonoTraversable
import           Data.Monoid                  (Endo(..))
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TypeLits
import           Data.Type.Product
import           GHC.Generics                 (Generic)
import           GHC.TypeLits
import           Numeric.BLAS hiding          (outer)
import           Numeric.LinearAlgebra.Static
import           Type.Family.List hiding      (Reverse)
import qualified Data.Vector                  as UV
import qualified Data.Vector.Generic.Sized    as VG
import qualified Data.Vector.Sized            as V
import qualified Data.Vector.Storable         as UVS
import qualified Data.Vector.Storable.Sized   as VS
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

    iamax
        :: forall n. KnownNat n
        => HM '[n + 1]
        -> Finite (n + 1)
    iamax  (HM x)        = withKnownNat (SNat @n %:+ SNat @1) $
        Finite . fromIntegral
      . LA.maxIndex . extract
      $ abs x

    gemv α (HM a) (HM x) = \case
        Just (β, HM y) -> HM (konst α * (a #> x) + konst β * y)
        Nothing        -> HM (konst α * (a #> x))
    ger  α (HM x) (HM y) = \case
        Just (HM a) -> HM (konst α * outer x y + a)
        Nothing     -> HM (konst α * outer x y)
    gemm α (HM a) (HM b) = \case
        Just (β, HM c) -> HM (konst α * (a <> b) + konst β * c)
        Nothing        -> HM (konst α * (a <> b))

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

    tslice
        :: forall n m. ()
        => ProdMap Slice n m
        -> HM n
        -> HM m
    tslice sl0 (HM x0) = HM $ go sl0 x0
      where
        go  :: forall ns ms. ()
            => ProdMap Slice ns ms
            -> HM' ns
            -> HM' ms
        go = \case
          PMZ -> \x -> x
          PMS (Slice sL sC@SNat sR) PMZ -> \xs -> fromJust . create $
            let l = fromIntegral $ fromSing sL
                c = fromIntegral $ fromSing sC
            in  withKnownNat (sL %:+ sC %:+ sR) $
                  LA.subVector l c (extract xs)
          PMS (Slice sLy sCy@SNat sRy) (PMS (Slice sLx sCx@SNat sRx) PMZ) ->
              \xs -> fromJust . create $
            let lx = fromIntegral $ fromSing sLx
                ly = fromIntegral $ fromSing sLy
                cx = fromIntegral $ fromSing sCx
                cy = fromIntegral $ fromSing sCy
            in  withKnownNat (sLy %:+ sCy %:+ sRy) $
                withKnownNat (sLx %:+ sCx %:+ sRx) $
                  LA.subMatrix (ly, lx) (cy, cx) (extract xs)
          PMS (Slice sL sC@SNat _) pm@(PMS _ (PMS _ _)) -> \xs ->
            let l = fromIntegral $ fromSing sL
                c = fromIntegral $ fromSing sC
            in  fmap (go pm)
                  . fromJust . V.toSized
                  . UV.take c
                  . UV.drop l
                  . V.fromSized
                  $ xs

    tconv
        :: forall n m s. ()
        => Sing n
        -> ProdMap Conv m s
        -> HM (m >: n)      -- ^ mask
        -> HM s
        -> HM (s >: n)
    tconv sn@SNat pm0 (HM m0) (HM x0) = HM $ go pm0 m0 x0
      where
        go  :: forall ms ss. ()
            => ProdMap Conv ms ss
            -> HM' (ms >: n)
            -> HM' ss
            -> HM' (ss >: n)
        go = \case
          PMZ -> \m x -> konst x * m
          PMS (Conv sM sS str off) PMZ -> \m x ->
            undefined

    treshape
        :: (SingI s1, Product s1 ~ Product s2)
        => Sing s2
        -> HM s1
        -> HM s2
    treshape s = unflatten s . flatten

    tload
        :: Sing s
        -> V.Vector (Product s) Double
        -> HM s
    tload s = unflatten s . VG.convert

    textract
        :: SingI s
        => HM s
        -> V.Vector (Product s) Double
    textract = VG.convert . flatten

-- hconv
--     :: forall o ms ns. (KnownNat o)
--     => DoubleProd Sing ms ns
--     -> HM' (o ': ms)
--     -> HM' ns
--     -> HM' (o ': ns)
-- hconv = \case
--     DPZ -> \ms x -> konst x * ms
--     DPS SNat sn@SNat DPZ -> \m x -> fromJust . create $
--       let c = LA.conv2 (extract m) (LA.asRow (extract x))
--           o = fromInteger (natVal (Proxy @o))
--           left = o `div` 2
--       in  LA.subMatrix (0,left) (o, fromInteger (fromSing sn)) c
--     DPS smx@SNat snx@SNat (DPS smy@SNat sny@SNat DPZ) -> \m x ->
--       -- todo: vectorize with im2colV
--       flip fmap m $ \msk -> fromJust . create $
--         let c = LA.conv2 (extract msk) (extract x)
--             left = fromInteger (fromSing smx) `div` 2
--             top  = fromInteger (fromSing smy) `div` 2
--         in  LA.subMatrix (left, top) (fromInteger (fromSing snx), fromInteger (fromSing sny)) c
--     dp0@(DPS (SNat :: Sing m0) (SNat :: Sing n0) (DPS _ _ (DPS _ _ _) :: DoubleProd Sing ms0 ns0)) ->
--               \(ms :: V.Vector o (V.Vector m0 (HM' ms0))) (xs :: V.Vector n0 (HM' ns0)) ->
--       flip fmap ms $ \(msk :: V.Vector m0 (HM' ms0)) -> hconv1 dp0 msk xs

-- hconv1
--     :: forall m s. ()
--     => DoubleProd Sing m s
--     -> HM' m
--     -> HM' s
--     -> HM' s
-- hconv1 = \case
--     DPZ -> (*)
--     DPS sm@SNat sn@SNat DPZ -> \m x -> fromJust . create $
--       let c = LA.conv (extract m) (extract x)
--           left = fromInteger (fromSing sm) `div` 2
--       in  UVS.slice left (fromInteger (fromSing sn)) c
--     DPS smx@SNat snx@SNat (DPS smy@SNat sny@SNat DPZ) -> \m x -> fromJust . create $
--       let c = LA.conv2 (extract m) (extract x)
--           left = fromInteger (fromSing smx) `div` 2
--           top  = fromInteger (fromSing smy) `div` 2
--       in  LA.subMatrix (left, top) (fromInteger (fromSing snx), fromInteger (fromSing sny)) c
--     DPS (SNat :: Sing m0) (SNat :: Sing n0) dps@(DPS _ _ (DPS _ _ _) :: DoubleProd Sing ms0 ns0) ->
--               \(ms :: V.Vector m0 (HM' ms0)) (xs :: V.Vector n0 (HM' ns0)) ->
--       let s   :: Sing ns0
--           s   = prodSing $ secondDP dps
--           cl :: V.Vector n0 (V.Vector m0 (HM' ns0))
--           cl = im2colV (hkonst s 0) xs
--       in  fmap (hsum s . V.zipWith (hconv1 dps) ms) cl

flatten :: SingI s => HM s -> VS.Vector (Product s) Double
flatten = hflatten sing . getHM

unflatten :: Sing s -> VS.Vector (Product s) Double -> HM s
unflatten s = HM . hunflatten s

hflatten
    :: Sing s
    -> HM' s
    -> VS.Vector (Product s) Double
hflatten = \case
    SNil -> VS.singleton
    SNat `SCons` SNil -> fromJust . VS.toSized . extract
    sn@SNat `SCons` (sm@SNat `SCons` SNil) -> case sn %:* sm of
      SNat -> fromJust . VS.toSized . LA.flatten . extract
    SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) ->
      VG.convert . V.concatMap (VG.convert . hflatten ns)

hunflatten
    :: Sing s
    -> VS.Vector (Product s) Double
    -> HM' s
hunflatten = \case
    SNil -> VS.head
    SNat `SCons` SNil -> fromJust . create . VS.fromSized
    SNat `SCons` (sm@SNat `SCons` SNil) -> fromJust . create . LA.reshape (fromInteger (fromSing sm)) . VS.fromSized
    sn@SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> case sProduct ns of
      sp@SNat -> fromJust
            . V.fromList
            . evalState (replicateM (fromInteger (fromSing sn)) $
                           hunflatten ns . fromJust . VS.toSized <$> state (UVS.splitAt (fromInteger (fromSing sp)))
                        )
            . VS.fromSized

im2col
    :: forall m n o. (KnownNat m, KnownNat n, KnownNat o)
    => L n m
    -> L n o
im2col = undefined

im2colV
    :: forall m n a. (KnownNat m, KnownNat n)
    => a
    -> V.Vector n a
    -> V.Vector n (V.Vector m a)
im2colV pad (V.fromSized->v) = V.generate $ \i ->
      fromJust . V.toSized $ UV.slice i m padded
  where
    padded = UV.concat [UV.replicate left pad, v, UV.replicate right pad]
    m :: Int
    m  = fromIntegral $ natVal (Proxy @m)
    left  = m `div` 2
    right = m - left

hadd :: Sing s -> HM' s -> HM' s -> HM' s
hadd = \case
    SNil                                     -> (+)
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

-- firstDP
--     :: DoubleProd f as bs
--     -> Prod f as
-- firstDP = \case
--     DPZ        -> Ø
--     DPS x _ xs -> x :< firstDP xs

-- secondDP
--     :: DoubleProd f as bs
--     -> Prod f bs
-- secondDP = \case
--     DPZ        -> Ø
--     DPS _ x xs -> x :< secondDP xs

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

helems :: forall s. SingI s => HM s -> [Double]
helems = flip appEndo [] . go sing . getHM
  where
    go :: Sing ns -> HM' ns -> Endo [Double]
    go = \case
      SNil                                      -> \x -> Endo (x:)
      SNat `SCons` SNil                         -> Endo . (++) . LA.toList . extract
      SNat `SCons` (SNat `SCons` SNil)          -> foldMap (Endo . (++)) . LA.toLists . extract
      SNat `SCons` ns@(_ `SCons` (_ `SCons` _)) -> foldMap (go ns)

instance SingI s => MonoFoldable (HM s) where
    ofoldMap f     = foldMap f . helems
    ofoldr f z     = foldr f z . helems
    ofoldl' f z    = foldl' f z . helems
    otoList        = helems
    oall f         = all f . helems
    oany f         = any f . helems
    onull          = (== 0) . olength
    olength _      = fromIntegral (product (fromSing (sing @_ @s)))
    olength64      = fromIntegral . olength
    ocompareLength = ocompareLength . helems
    otraverse_ f   = traverse_ f . helems
    ofor_ x        = for_ (helems x)
    omapM_ f       = traverse_ f . helems
    oforM_ x       = for_ (helems x)
    ofoldlM f x    = foldlM f x . helems
    ofoldMap1Ex f  = ofoldMap1Ex f . helems
    ofoldr1Ex f    = ofoldr1Ex f . helems
    ofoldl1Ex' f   = ofoldl1Ex' f . helems
    headEx         = headEx . helems
    lastEx         = lastEx . helems
    maximumByEx f  = maximumByEx f . helems
    minimumByEx f  = minimumByEx f . helems

deriving instance NFData (HM' s)     => NFData (HM s)
deriving instance Show (HM' s)       => Show (HM s)
deriving instance Num (HM' s)        => Num (HM s)
deriving instance Fractional (HM' s) => Fractional (HM s)
deriving instance Floating (HM' s)   => Floating (HM s)

