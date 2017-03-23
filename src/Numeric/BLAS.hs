{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Numeric.BLAS (
    BLAS(..)
  , BShape'(..)
  , BShape, BV, BM
  , Sing(SBV, SBM)
  , SBShape'
  , BIndex(..)
  , sBshapeSize
  , bshapeSize
  , matVec
  , vecMat
  , outer
  , matVecOp
  , dotOp
  ) where

import           Data.Finite
import           Data.Kind
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           GHC.TypeLits
import           Numeric.Backprop.Op
import           Type.Class.Higher

$(singletons [d|
  data BShape' a = BV !a | BM !a !a
    deriving (Show, Eq, Ord, Functor)

  bshapeSize :: Num a => BShape' a -> a
  bshapeSize (BV x  ) = x
  bshapeSize (BM x y) = x * y
  |])

type BShape = BShape' Nat
type BV = 'BV
type BM = 'BM

data BIndex :: BShape -> Type where
    BVIx :: Finite n -> BIndex (BV n)
    BMIx :: Finite m -> Finite n -> BIndex (BM m n)

deriving instance Eq (BIndex s)
instance Eq1 BIndex where
    eq1 = \case
      BVIx i -> \case
        BVIx i' -> i == i'
      BMIx i j -> \case
        BMIx i' j' -> i == i' && j == j'
    neq1 = \case
      BVIx i -> \case
        BVIx i' -> i /= i'
      BMIx i j -> \case
        BMIx i' j' -> i /= i' || j /= j'


class RealFloat (Scalar b) => BLAS (b :: BShape -> Type) where
    type Scalar b :: Type

    bkonst
        :: Sing s
        -> Scalar b
        -> b s

    transp
        :: (KnownNat m, KnownNat n)
        => b (BM m n)
        -> b (BM n m)


    -- Level 1
    scal
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b (BV n)    -- ^ x
        -> b (BV n)    -- ^ α x

    axpy
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b (BV n)    -- ^ x
        -> b (BV n)    -- ^ y
        -> b (BV n)    -- ^ α x + y

    dot :: KnownNat n
        => b (BV n)    -- ^ x
        -> b (BV n)    -- ^ y
        -> Scalar b     -- ^ x' y

    norm2
        :: KnownNat n
        => b (BV n)    -- ^ x
        -> Scalar b     -- ^ ||x||

    asum
        :: KnownNat n
        => b (BV n)    -- ^ x
        -> Scalar b     -- ^ sum_i |x_i|

    iamax
        :: KnownNat n
        => b (BV n)    -- ^ x
        -> Finite n     -- ^ argmax_i |x_i|

    -- Level 2
    gemv
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b (BM m n)  -- ^ A
        -> b (BV n)    -- ^ x
        -> Maybe (Scalar b, b (BV m))    -- ^ β, y
        -> b (BV m)    -- ^ α A x + β y

    ger :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b (BV m)    -- ^ x
        -> b (BV n)    -- ^ y
        -> Maybe (b (BM m n))  -- ^ A
        -> b (BM m n)  -- ^ x y' + A

    syr :: KnownNat n
        => Scalar b     -- ^ α
        -> b (BV n)    -- ^ x
        -> b (BM n n)  -- ^ A
        -> b (BM n n)  -- ^ x x' + A

    -- Level 3
    gemm
        :: (KnownNat m, KnownNat o, KnownNat n)
        => Scalar b     -- ^ α
        -> b (BM m o)  -- ^ A
        -> b (BM o n)  -- ^ B
        -> Maybe (Scalar b, b (BM m n))  -- ^ β, C
        -> b (BM m n)  -- ^ α A B + β C

    syrk
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b (BM m n)  -- ^ A
        -> Scalar b     -- ^ β
        -> b (BM m m)  -- ^ C
        -> b (BM m m)  -- ^ α A A' + β C

matVec
    :: (KnownNat m, KnownNat n, BLAS b)
    => b (BM m n)
    -> b (BV n)
    -> b (BV m)
matVec a x = gemv 1 a x Nothing

vecMat
    :: (KnownNat m, KnownNat n, BLAS b)
    => b (BV m)
    -> b (BM m n)
    -> b (BV n)
vecMat x a = gemv 1 (transp a) x Nothing

outer
    :: (KnownNat m, KnownNat n, BLAS b)
    => b (BV m)
    -> b (BV n)
    -> b (BM m n)
outer x y = ger 1 x y Nothing

matVecOp
    :: (KnownNat m, KnownNat n, BLAS b)
    => Op '[ b (BM m n), b (BV n) ] '[ b (BV m) ]
matVecOp = op2' $ \a x ->
    ( only_ (matVec a x)
    , (\g -> (outer g x, vecMat g a))
    . fromMaybe (bkonst sing 1)
    . head'
    )

dotOp
    :: forall b n. (KnownNat n, BLAS b)
    => Op '[ b (BV n), b (BV n) ] '[ Scalar b ]
dotOp = op2' $ \x y ->
    ( only_ (dot x y)
    , \case Nothing :< Ø -> (y       , x       )
            Just g  :< Ø -> (scal g y, scal g x)
    )
