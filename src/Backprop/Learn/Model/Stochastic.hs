{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE ViewPatterns          #-}

module Backprop.Learn.Model.Stochastic (
    DO(..)
  , StochFunc(..)
  , FixedStochFunc, pattern FSF, _fsfRunDeterm, _fsfRunStoch
  , rreLU
  , injectNoise
  ) where

import           Backprop.Learn.Model
import           Backprop.Learn.Model.Function
import           Control.Monad.Primitive
import           Data.Bool
import           Data.Kind
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Statistics.Distribution               as Stat
import qualified System.Random.MWC                     as MWC

-- | Dropout layer.  Parameterized by dropout percentage (should be between
-- 0 and 1).
--
-- 0 corresponds to no dropout, 1 corresponds to complete dropout of all
-- nodes every time.
newtype DO (n :: Nat) = DO { _doRate :: Double }

instance KnownNat n => Learn (R n) (R n) (DO n) where
    runLearn (DO r) _ = stateless (constVar (realToFrac (1-r)) *)
    runLearnStoch (DO r) g _ = statelessM $ \x ->
        (x *) . constVar . vecR <$> SVS.replicateM (mask g)
      where
        mask = fmap (bool 1 0 . (<= r))
             . MWC.uniform

-- | Represents a random-valued function, with a possible trainable
-- parameter.
--
-- Requires both a "deterministic" and a "stochastic" mode.  The
-- deterministic mode ideally should approximate some mean of the
-- stochastic mode.
data StochFunc :: Maybe Type -> Type -> Type -> Type where
    SF :: { _sfInitParam :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m p
          , _sfRunDeterm :: forall s. Reifies s W => Mayb (BVar s) p -> BVar s a -> BVar s b
          , _sfRunStoch
              :: forall m s. (PrimMonad m, Reifies s W)
              => MWC.Gen (PrimState m)
              -> Mayb (BVar s) p
              -> BVar s a
              -> m (BVar s b)
          }
       -> StochFunc p a b

instance Learn a b (StochFunc p a b) where
    type LParamMaybe (StochFunc p a b) = p
    type LStateMaybe (StochFunc p a b) = 'Nothing

    initParam (SF i _ _) = i

    runLearn (SF _ r _)        = stateless . r
    runLearnStoch (SF _ _ r) g = statelessM . r g

-- | Convenient alias for a 'StochFunc' (random-valued function with both
-- deterministic and stochastic modes) with no trained parameters.
type FixedStochFunc = StochFunc 'Nothing

-- | Construct a 'FixedStochFunc'
pattern FSF :: (forall s. Reifies s W => BVar s a -> BVar s b)
            -> (forall m s. (PrimMonad m, Reifies s W) => MWC.Gen (PrimState m) -> BVar s a -> m (BVar s b))
            -> FixedStochFunc a b
pattern FSF { _fsfRunDeterm, _fsfRunStoch } <- (getFSF->(getWD->_fsfRunDeterm,getWS->_fsfRunStoch))
  where
    FSF d s = SF { _sfInitParam = const N_
                 , _sfRunDeterm = const d
                 , _sfRunStoch  = const . s
                 }

newtype WrapDeterm a b = WD { getWD :: forall s. Reifies s W => BVar s a -> BVar s b }
newtype WrapStoch  a b = WS { getWS :: forall m s. (PrimMonad m, Reifies s W) => MWC.Gen (PrimState m) -> BVar s a -> m (BVar s b) }

getFSF :: FixedStochFunc a b -> (WrapDeterm a b, WrapStoch a b)
getFSF (SF _ d s) = ( WD (d N_)
                    , WS (`s` N_)
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
injectNoise
    :: (Stat.ContGen d, Stat.Mean d, KnownNat n)
    => d
    -> FixedStochFunc (R n) (R n)
injectNoise d = FSF { _fsfRunDeterm = (realToFrac (Stat.mean d) +)
                    , _fsfRunStoch  = \g x -> do
                        e <- vecR <$> SVS.replicateM (Stat.genContVar d g)
                        pure (constVar e + x)
                    }
