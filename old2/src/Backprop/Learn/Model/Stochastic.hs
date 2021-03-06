{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Backprop.Learn.Model.Stochastic (
    DO(..)
  , StochFunc(..)
  , FixedStochFunc, pattern FSF, _fsfRunDeterm, _fsfRunStoch
  , rreLU
  , injectNoise, applyNoise
  , injectNoiseR, applyNoiseR
  ) where

import           Backprop.Learn.Model.Class
import           Backprop.Learn.Model.Function
import           Control.Monad.Primitive
import           Data.Bool
import           Data.Kind
import           Data.Typeable
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Statistics.Distribution               as Stat
import qualified System.Random.MWC                     as MWC
import qualified System.Random.MWC.Distributions       as MWC

-- | Dropout layer.  Parameterized by dropout percentage (should be between
-- 0 and 1).
--
-- 0 corresponds to no dropout, 1 corresponds to complete dropout of all
-- nodes every time.
newtype DO (n :: Nat) = DO { _doRate :: Double }
  deriving (Typeable)

instance KnownNat n => Learn (R n) (R n) (DO n) where
    runLearn (DO r) _ = stateless (constVar (realToFrac (1-r)) *)
    runLearnStoch (DO r) g _ = statelessM $ \x ->
        (x *) . constVar . vecR <$> SVS.replicateM (mask g)
      where
        mask = fmap (bool 1 0) . MWC.bernoulli r

-- | Represents a random-valued function, with a possible trainable
-- parameter.
--
-- Requires both a "deterministic" and a "stochastic" mode.  The
-- deterministic mode ideally should approximate some mean of the
-- stochastic mode.
data StochFunc :: Maybe Type -> Type -> Type -> Type where
    SF :: { _sfRunDeterm :: forall s. Reifies s W => Mayb (BVar s) p -> BVar s a -> BVar s b
          , _sfRunStoch
              :: forall m s. (PrimMonad m, Reifies s W)
              => MWC.Gen (PrimState m)
              -> Mayb (BVar s) p
              -> BVar s a
              -> m (BVar s b)
          }
       -> StochFunc p a b
  deriving (Typeable)

instance Learn a b (StochFunc p a b) where
    type LParamMaybe (StochFunc p a b) = p
    type LStateMaybe (StochFunc p a b) = 'Nothing

    runLearn SF{..} = stateless . _sfRunDeterm
    runLearnStoch SF{..} g = statelessM . _sfRunStoch g

-- | Convenient alias for a 'StochFunc' (random-valued function with both
-- deterministic and stochastic modes) with no trained parameters.
type FixedStochFunc = StochFunc 'Nothing

-- | Construct a 'FixedStochFunc'
pattern FSF :: (forall s. Reifies s W => BVar s a -> BVar s b)
            -> (forall m s. (PrimMonad m, Reifies s W) => MWC.Gen (PrimState m) -> BVar s a -> m (BVar s b))
            -> FixedStochFunc a b
pattern FSF { _fsfRunDeterm, _fsfRunStoch } <- (getFSF->(getWD->_fsfRunDeterm,getWS->_fsfRunStoch))
  where
    FSF d s = SF { _sfRunDeterm = const d
                 , _sfRunStoch  = const . s
                 }
{-# COMPLETE FSF #-}

newtype WrapDeterm a b = WD { getWD :: forall s. Reifies s W => BVar s a -> BVar s b }
newtype WrapStoch  a b = WS { getWS :: forall m s. (PrimMonad m, Reifies s W) => MWC.Gen (PrimState m) -> BVar s a -> m (BVar s b) }

getFSF :: FixedStochFunc a b -> (WrapDeterm a b, WrapStoch a b)
getFSF SF{..} = ( WD (_sfRunDeterm N_)
                , WS (`_sfRunStoch` N_)
                )

-- | Random leaky rectified linear unit
rreLU
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> FixedStochFunc (R n) (R n)
rreLU d = FSF { _fsfRunDeterm = vmap' (preLU v)
              , _fsfRunStoch  = \g x -> do
                  α <- vecR <$> SVS.replicateM (Stat.genContVar d g)
                  pure (zipWithVector preLU (constVar α) x)
              }
  where
    v :: BVar s Double
    v = constVar (Stat.mean d)

-- | Inject random noise.  Usually used between neural network layers, or
-- at the very beginning to pre-process input.
--
-- In non-stochastic mode, this adds the mean of the distribution.
injectNoise
    :: (Stat.ContGen d, Stat.Mean d, Fractional a)
    => d
    -> FixedStochFunc a a
injectNoise d = FSF { _fsfRunDeterm = (realToFrac (Stat.mean d) +)
                    , _fsfRunStoch  = \g x -> do
                        e <- Stat.genContVar d g
                        pure (realToFrac e + x)
                    }


-- | 'injectNoise' lifted to 'R'
injectNoiseR
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> FixedStochFunc (R n) (R n)
injectNoiseR d = FSF { _fsfRunDeterm = (realToFrac (Stat.mean d) +)
                     , _fsfRunStoch  = \g x -> do
                         e <- vecR <$> SVS.replicateM (Stat.genContVar d g)
                         pure (constVar e + x)
                     }

-- | Multply by random noise.  Can be used to implement dropout-like
-- behavior.
--
-- In non-stochastic mode, this scales by the mean of the distribution.
applyNoise
    :: (Stat.ContGen d, Stat.Mean d, Fractional a)
    => d
    -> FixedStochFunc a a
applyNoise d = FSF { _fsfRunDeterm = (realToFrac (Stat.mean d) *)
                   , _fsfRunStoch  = \g x -> do
                       e <- Stat.genContVar d g
                       pure (realToFrac e * x)
                   }

-- | 'applyNoise' lifted to 'R'
applyNoiseR
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> FixedStochFunc (R n) (R n)
applyNoiseR d = FSF { _fsfRunDeterm = (realToFrac (Stat.mean d) *)
                   , _fsfRunStoch  = \g x -> do
                       e <- vecR <$> SVS.replicateM (Stat.genContVar d g)
                       pure (constVar e * x)
                   }
