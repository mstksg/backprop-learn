{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}

module Numeric.BLAS.HMatrix (
    HM(..)
  , HM'
  ) where

import           Data.Finite.Internal
import           Data.Foldable
import           Data.Kind
import           Data.MonoTraversable
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Numeric.BLAS
import           Numeric.LinearAlgebra.Static
import qualified Numeric.LinearAlgebra        as LA

type family HM' (s :: BShape Nat) :: Type where
    HM' ('BV n  ) = R n
    HM' ('BM m n) = L m n

newtype HM :: BShape Nat -> Type where
    HM  :: { getHM :: HM' b }
        -> HM b

type instance Element (HM s) = Double

instance BLAS HM where
    type Scalar HM = Double

    scal α (HM x)        = HM (konst α * x)
    axpy α (HM x) (HM y) = HM (konst α * x + y)
    dot    (HM x) (HM y) = x <.> y
    norm2  (HM x)        = norm_2 x
    asum   (HM x)        = norm_1 x
    iamax  (HM x)        = Finite . fromIntegral
                         . LA.maxIndex . extract
                         $ abs x

    gemv α (HM a) (HM x) β (HM y) = HM (konst α * (a #> x) + konst β * y)
    ger  α (HM x) (HM y) (HM a)   = HM (konst α * outer x y + a)
    syr  α (HM x) (HM a)          = HM (konst α * outer x x + a)
    gemm α (HM a) (HM b) β (HM c) = HM (konst α * (a <> b) + konst β * c)
    syrk α (HM a) β (HM c)        = HM (konst α * (a <> tr a) + konst β * c)

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


