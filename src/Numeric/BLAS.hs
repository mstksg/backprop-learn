{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Numeric.BLAS (
    BLAS(..)
  , BShape(..)
  , Sing(SBV, SBM)
  , SBShape
  , BIndex(..)
  ) where

import           Data.Finite
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           GHC.TypeLits

$(singletons [d|
  data BShape a = BV !a | BM !a !a
    deriving (Show, Eq, Ord, Functor)

  bshapeSize :: Num a => BShape a -> a
  bshapeSize (BV x  ) = x
  bshapeSize (BM x y) = x * y
  |])

data BIndex :: BShape Nat -> Type where
    BVIx :: Finite n -> BIndex ('BV n)
    BMIx :: Finite m -> Finite n -> BIndex ('BM m n)

class RealFloat (Scalar b) => BLAS (b :: BShape Nat -> Type) where
    type Scalar b :: Type

    -- Level 1
    scal
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b ('BV n)    -- ^ x
        -> b ('BV n)    -- ^ α x

    axpy
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b ('BV n)    -- ^ x
        -> b ('BV n)    -- ^ y
        -> b ('BV n)    -- ^ α x + y

    dot :: KnownNat n
        => b ('BV n)    -- ^ x
        -> b ('BV n)    -- ^ y
        -> Scalar b     -- ^ x' y

    norm2
        :: KnownNat n
        => b ('BV n)    -- ^ x
        -> Scalar b     -- ^ ||x||

    asum
        :: KnownNat n
        => b ('BV n)    -- ^ x
        -> Scalar b     -- ^ sum_i |x_i|

    iamax
        :: KnownNat n
        => b ('BV n)    -- ^ x
        -> Finite n     -- ^ argmax_i |x_i|

    -- Level 2
    gemv
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b ('BM m n)  -- ^ A
        -> b ('BV n)    -- ^ x
        -> Scalar b     -- ^ β
        -> b ('BV m)    -- ^ y
        -> b ('BV m)    -- ^ α A x + β y

    ger :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b ('BV m)    -- ^ x
        -> b ('BV n)    -- ^ y
        -> b ('BM m n)  -- ^ A
        -> b ('BM m n)  -- ^ x y' + A

    syr :: KnownNat n
        => Scalar b     -- ^ α
        -> b ('BV n)    -- ^ x
        -> b ('BM n n)  -- ^ A
        -> b ('BM n n)  -- ^ x x' + A

    -- Level 3
    gemm
        :: (KnownNat m, KnownNat o, KnownNat n)
        => Scalar b     -- ^ α
        -> b ('BM m o)  -- ^ A
        -> b ('BM o n)  -- ^ B
        -> Scalar b     -- ^ β
        -> b ('BM m n)  -- ^ C
        -> b ('BM m n)  -- ^ α A B + β C

    syrk
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b ('BM m n)  -- ^ A
        -> Scalar b     -- ^ β
        -> b ('BM m m)  -- ^ C
        -> b ('BM m m)  -- ^ α A A' + β C
