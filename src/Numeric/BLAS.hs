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
  , amax
  , concretize
  , matVecOp
  , dotOp
  , asumOp
  , module Numeric.Tensor
  ) where

import           Data.Finite
import           Data.Finite.Internal
import           Data.Foldable hiding     (asum)
import           Data.Kind
import           Data.Maybe
import           Data.Ord
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Numeric.Backprop.Op
import           Numeric.Tensor

class Tensor b => BLAS (b :: [Nat] -> Type) where

    transp
        :: (KnownNat m, KnownNat n)
        => b '[m, n]
        -> b '[n, m]
    transp x = gen sing $ \case
        n :< m :< Ø -> tindex (m :< n :< Ø) x

    -- Level 1
    scal
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b '[n]    -- ^ x
        -> b '[n]    -- ^ α x
    scal α = tmap (α *)

    axpy
        :: KnownNat n
        => Scalar b     -- ^ α
        -> b '[n]    -- ^ x
        -> b '[n]    -- ^ y
        -> b '[n]    -- ^ α x + y
    axpy α = tzip (\x y -> α * x + y)

    dot :: KnownNat n
        => b '[n]    -- ^ x
        -> b '[n]    -- ^ y
        -> Scalar b     -- ^ x' y
    dot x y = tsum (tzip (*) x y)

    norm2
        :: KnownNat n
        => b '[n]    -- ^ x
        -> Scalar b     -- ^ ||x||
    norm2 = tsum . tmap (** 2)

    asum
        :: KnownNat n
        => b '[n]    -- ^ x
        -> Scalar b     -- ^ sum_i |x_i|
    asum = tsum . tmap abs

    iamax
        :: KnownNat n
        => b '[n]    -- ^ x
        -> Finite n     -- ^ argmax_i |x_i|
    iamax = Finite . fst . maximumBy (comparing snd) . zip [0..] . tlist . tmap abs

    -- Level 2
    gemv
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m, n]  -- ^ A
        -> b '[n]    -- ^ x
        -> Maybe (Scalar b, b '[m])    -- ^ β, y
        -> b '[m]    -- ^ α A x + β y
    gemv α a x b = maybe id (uncurry axpy) b . gen sing $ \case
        i :< Ø -> α * dot x (treshape sing (tslice (SliceSingle i `PMS` SliceAll `PMS` PMZ) a))

    ger :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m]    -- ^ x
        -> b '[n]    -- ^ y
        -> Maybe (b '[m, n])  -- ^ A
        -> b '[m, n]  -- ^ α x y' + A
    ger α x y b = maybe id (tzip (+)) b . gen sing $ \case
        i :< j :< Ø -> α * tindex (i :< Ø) x * tindex (j :< Ø) y

    syr :: KnownNat n
        => Scalar b           -- ^ α
        -> b '[n]             -- ^ x
        -> Maybe (b '[n, n])  -- ^ A
        -> b '[n, n]          -- ^ x x' + A
    syr α x a = ger α x x a

    -- Level 3
    gemm
        :: (KnownNat m, KnownNat o, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m, o]  -- ^ A
        -> b '[o, n]  -- ^ B
        -> Maybe (Scalar b, b '[m, n])  -- ^ β, C
        -> b '[m, n]  -- ^ α A B + β C
    gemm α a b c = maybe id (uncurry f) c . gen sing $ \case
        i :< j :< Ø ->
            α * dot (treshape sing (tslice (SliceSingle i `PMS` SliceAll `PMS` PMZ) a))
                    (treshape sing (tslice (SliceAll `PMS` SliceSingle j `PMS` PMZ) b))
      where
        f β = tzip (\d r -> β * d + r)

    syrk
        :: (KnownNat m, KnownNat n)
        => Scalar b     -- ^ α
        -> b '[m, n]  -- ^ A
        -> Maybe (Scalar b, b '[m, m])  -- ^ β, C
        -> b '[m, m]  -- ^ α A A' + β C
    syrk α a c = gemm α a (transp a) c

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

amax
    :: (BLAS b, KnownNat n)
    => b '[n]
    -> Scalar b
amax = do
    i <- only . iamax
    tindex i

concretize :: (BLAS b, KnownNat n) => b '[n] -> b '[n]
concretize = oneHot . only . iamax

matVecOp
    :: (KnownNat m, KnownNat n, BLAS b)
    => Op '[ b '[m, n], b '[n] ] '[ b '[m] ]
matVecOp = op2' $ \a x ->
    ( only_ (matVec a x)
    , (\g -> (outer g x, vecMat g a))
    . fromMaybe (tkonst sing 1)
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
