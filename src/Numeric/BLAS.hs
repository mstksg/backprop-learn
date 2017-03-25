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
  , matVec
  , vecMat
  , outer
  , matVecOp
  , dotOp
  , asumOp
  , module Numeric.Tensor
  ) where

import           Data.Finite
import           Data.Kind
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude
import           Data.Singletons.TH
import           GHC.TypeLits
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           Type.Class.Higher

-- $(singletons [d|
--   data [Nat]' a = BV !a | BM !a !a
--     deriving (Show, Eq, Ord, Functor)

--   bshapeSize :: Num a => [Nat]' a -> a
--   bshapeSize (BV x  ) = x
--   bshapeSize (BM x y) = x * y
--   |])

-- type [Nat] = [Nat]' Nat
-- type BV = 'BV
-- type BM = 'BM

-- data BIndex :: [Nat] -> Type where
--     BVIx :: Finite n -> BIndex '[n]
--     BMIx :: Finite m -> Finite n -> BIndex (BM m n)

-- deriving instance Eq (BIndex s)
-- instance Eq1 BIndex where
--     eq1 = \case
--       BVIx i -> \case
--         BVIx i' -> i == i'
--       BMIx i j -> \case
--         BMIx i' j' -> i == i' && j == j'
--     neq1 = \case
--       BVIx i -> \case
--         BVIx i' -> i /= i'
--       BMIx i j -> \case
--         BMIx i' j' -> i /= i' || j /= j'


class Tensor b => BLAS (b :: [Nat] -> Type) where

    bkonst
        :: Sing s
        -> Scalar b
        -> b s

    transp
        :: (KnownNat m, KnownNat n)
        => b '[m, n]
        -> b '[n, m]


    -- Level 1
    scal
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b '[n]    -- ^ x
        -> b '[n]    -- ^ α x

    axpy
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b '[n]    -- ^ x
        -> b '[n]    -- ^ y
        -> b '[n]    -- ^ α x + y

    dot :: KnownNat n
        => b '[n]    -- ^ x
        -> b '[n]    -- ^ y
        -> Scalar b     -- ^ x' y

    norm2
        :: KnownNat n
        => b '[n]    -- ^ x
        -> Scalar b     -- ^ ||x||

    asum
        :: KnownNat n
        => b '[n]    -- ^ x
        -> Scalar b     -- ^ sum_i |x_i|

    iamax
        :: KnownNat n
        => b '[n]    -- ^ x
        -> Finite n     -- ^ argmax_i |x_i|

    -- Level 2
    gemv
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m, n]  -- ^ A
        -> b '[n]    -- ^ x
        -> Maybe (Scalar b, b '[m])    -- ^ β, y
        -> b '[m]    -- ^ α A x + β y

    ger :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m]    -- ^ x
        -> b '[n]    -- ^ y
        -> Maybe (b '[m, n])  -- ^ A
        -> b '[m, n]  -- ^ x y' + A

    syr :: KnownNat n
        => Scalar b     -- ^ α
        -> b '[n]    -- ^ x
        -> b '[n, n]  -- ^ A
        -> b '[n, n]  -- ^ x x' + A

    -- Level 3
    gemm
        :: (KnownNat m, KnownNat o, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m, o]  -- ^ A
        -> b '[o, n]  -- ^ B
        -> Maybe (Scalar b, b '[m, n])  -- ^ β, C
        -> b '[m, n]  -- ^ α A B + β C

    syrk
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m, n]  -- ^ A
        -> Scalar b     -- ^ β
        -> b '[m, m]  -- ^ C
        -> b '[m, m]  -- ^ α A A' + β C

matVec
    :: (KnownNat m, KnownNat n, BLAS b)
    => b '[m, n]
    -> b '[n]
    -> b '[m]
matVec a x = gemv 1 a x Nothing

vecMat
    :: (KnownNat m, KnownNat n, BLAS b)
    => b '[m]
    -> b '[m, n]
    -> b '[n]
vecMat x a = gemv 1 (transp a) x Nothing

outer
    :: (KnownNat m, KnownNat n, BLAS b)
    => b '[m]
    -> b '[n]
    -> b '[m, n]
outer x y = ger 1 x y Nothing

matVecOp
    :: (KnownNat m, KnownNat n, BLAS b)
    => Op '[ b '[m, n], b '[n] ] '[ b '[m] ]
matVecOp = op2' $ \a x ->
    ( only_ (matVec a x)
    , (\g -> (outer g x, vecMat g a))
    . fromMaybe (bkonst sing 1)
    . head'
    )

dotOp
    :: forall b n. (KnownNat n, BLAS b)
    => Op '[ b '[n], b '[n] ] '[ Scalar b ]
dotOp = op2' $ \x y ->
    ( only_ (dot x y)
    , \case Nothing :< Ø -> (y       , x       )
            Just g  :< Ø -> (scal g y, scal g x)
    )

asumOp
    :: forall b n. (KnownNat n, BLAS b, Num (b '[n]))
    => Op '[ b '[n] ] '[ Scalar b ]
asumOp = op1' $ \x ->
    ( only_ (asum x)
    , \case Nothing :< Ø -> signum x
            Just g  :< Ø -> scal g (signum x)
    )
