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

module Backprop.Learn.Initialize (
    Initialize(..)
  , gInitialize
  , initializeNormal
  , initializeSingle
  ) where

import           Control.Monad.Primitive
import           Data.Complex
import           Data.Type.Length
import           Data.Type.NonEmpty
import           Data.Type.Tuple
import           GHC.TypeNats
import           Generics.OneLiner
import           Numeric.LinearAlgebra.Static.Vector
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import           Type.Class.Known
import           Type.Family.List
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
instance (Initialize a, Initialize b) => Initialize (T2 a b)
instance (Initialize a, Initialize b, Initialize c) => Initialize (T3 a b c)

instance (ListC (Initialize <$> as), Known Length as) => Initialize (T as) where
    initialize d g = constTA @Initialize (initialize d g) known

instance (Initialize a, ListC (Initialize <$> as), Known Length as) => Initialize (NETup (a ':| as)) where
    initialize d g = NET <$> initialize d g
                         <*> initialize d g

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


constTA
    :: forall c as f. (ListC (c <$> as), Applicative f)
    => (forall a. c a => f a)
    -> Length as
    -> f (T as)
constTA x = go
  where
    go :: forall bs. ListC (c <$> bs) => Length bs -> f (T bs)
    go LZ     = pure TNil
    go (LS l) = (:&) <$> x <*> go l

