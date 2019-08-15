{-# LANGUAGE AllowAmbiguousTypes                      #-}
{-# LANGUAGE ConstraintKinds                          #-}
{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE DefaultSignatures                        #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Initialize (
    Initialize(..)
  , gInitialize
  , initializeNormal
  , initializeSingle
  -- * Reshape
  , reshapeR
  , reshapeLRows
  , reshapeLCols
  ) where

import           Control.Monad.Primitive
import           Data.Complex
import           Data.Proxy
import           Data.Type.Equality
import           Data.Type.Tuple
import           Data.Vinyl
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import           Generics.OneLiner
import           Numeric.LinearAlgebra.Static.Vector
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Data.Vector.Generic                 as VG
import qualified Data.Vector.Generic.Sized           as SVG
import qualified Numeric.LinearAlgebra.Static        as H
import qualified System.Random.MWC                   as MWC

-- | Class for types that are basically a bunch of 'Double's, which can be
-- initialized with a given identical and independent distribution.
class Initialize p where
    initialize
        :: (ContGen d, PrimMonad m)
        => d
        -> MWC.Gen (PrimState m)
        -> m p

    default initialize
        :: (ADTRecord p, Constraints p Initialize, ContGen d, PrimMonad m)
        => d
        -> MWC.Gen (PrimState m)
        -> m p
    initialize = gInitialize

-- | 'initialize' for any instance of 'Generic'.
gInitialize
    :: (ADTRecord p, Constraints p Initialize, ContGen d, PrimMonad m)
    => d
    -> MWC.Gen (PrimState m)
    -> m p
gInitialize d g = createA' @Initialize (initialize d g)

-- | Helper over 'inititialize' for a gaussian distribution centered around
-- zero.
initializeNormal
    :: (Initialize p, PrimMonad m)
    => Double                               -- ^ standard deviation
    -> MWC.Gen (PrimState m)
    -> m p
initializeNormal = initialize . normalDistr 0

-- | 'initialize' definition if @p@ is a single number.
initializeSingle
    :: (ContGen d, PrimMonad m, Fractional p)
    => d
    -> MWC.Gen (PrimState m)
    -> m p
initializeSingle d = fmap realToFrac . genContVar d

instance Initialize Double where
    initialize = initializeSingle
instance Initialize Float where
    initialize = initializeSingle

-- | Initializes real and imaginary components identically
instance Initialize a => Initialize (Complex a) where

instance Initialize T0
instance Initialize a => Initialize (TF a)
instance (Initialize a, Initialize b) => Initialize (a :# b)

instance RPureConstrained Initialize as => Initialize (T as) where
    initialize d g = rtraverse (fmap TF)
                   $ rpureConstrained @Initialize (initialize d g)

-- instance (Initialize a, ListC (Initialize <$> as), Known Length as) => Initialize (NETup (a ':| as)) where
--     initialize d g = NET <$> initialize d g
--                          <*> initialize d g

instance Initialize ()
instance (Initialize a, Initialize b) => Initialize (a, b)
instance (Initialize a, Initialize b, Initialize c) => Initialize (a, b, c)

instance (VG.Vector v a, KnownNat n, Initialize a) => Initialize (SVG.Vector v n a) where
    initialize d = SVG.replicateM . initialize d

instance KnownNat n => Initialize (H.R n) where
    initialize d = fmap vecR . initialize d
instance KnownNat n => Initialize (H.C n) where
    initialize d = fmap vecC . initialize d

instance (KnownNat n, KnownNat m) => Initialize (H.L n m) where
    initialize d = fmap vecL . initialize d
instance (KnownNat n, KnownNat m) => Initialize (H.M n m) where
    initialize d = fmap vecM . initialize d

-- | Reshape a vector to have a different amount of items  If the matrix is
-- grown, new weights are initialized according to the given distribution.
reshapeR
    :: forall i j d m. (ContGen d, PrimMonad m, KnownNat i, KnownNat j)
    => d
    -> MWC.Gen (PrimState m)
    -> H.R i
    -> m (H.R j)
reshapeR d g x = case Proxy @j %<=? Proxy @i of
    LE  Refl      -> pure . vecR . SVG.take @_ @j @(i - j) . rVec $ x
    NLE Refl Refl -> (x H.#) <$> initialize @(H.R (j - i)) d g

-- | Reshape a matrix to have a different amount of rows  If the matrix
-- is grown, new weights are initialized according to the given
-- distribution.
reshapeLRows
    :: forall i j n d m. (ContGen d, PrimMonad m, KnownNat n, KnownNat i, KnownNat j)
    => d
    -> MWC.Gen (PrimState m)
    -> H.L i n
    -> m (H.L j n)
reshapeLRows d g x = case Proxy @j %<=? Proxy @i of
    LE Refl       -> pure . rowsL . SVG.take @_ @j @(i - j) . lRows $ x
    NLE Refl Refl -> (x H.===) <$> initialize @(H.L (j - i) n) d g

-- | Reshape a matrix to have a different amount of columns.  If the matrix
-- is grown, new weights are initialized according to the given
-- distribution.
reshapeLCols
    :: forall i j n d m. (ContGen d, PrimMonad m, KnownNat n, KnownNat i, KnownNat j)
    => d
    -> MWC.Gen (PrimState m)
    -> H.L n i
    -> m (H.L n j)
reshapeLCols d g x = case Proxy @j %<=? Proxy @i of
    LE Refl       -> pure . colsL . SVG.take @_ @j @(i - j) . lCols $ x
    NLE Refl Refl -> (x H.|||) <$> initialize @(H.L n (j - i)) d g
