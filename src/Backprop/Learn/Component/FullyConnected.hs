{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Backprop.Learn.Component.FullyConnected (
    FC(..), fc
  , FCP(..), fcBias, fcWeights
  ) where


import           Backprop.Learn.Class
import           Control.Monad.Primitive
import           GHC.Generics                          (Generic)
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.OneLiner
import           Statistics.Distribution
import qualified Data.Vector.Storable.Sized            as SVS
import qualified System.Random.MWC                     as MWC


-- | Fully connected feed-forward layer with bias.  Parameterized by its
-- initialization distribution.
newtype FC (i :: Nat) (o :: Nat) =
    FC { _fcGen :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
       }

-- | Construct an @'FC' i o@ using a given distribution from the
-- /statistics/ library.
fc :: ContGen d => d -> FC i o
fc d = FC (genContVar d)

-- | Fully connected feed-forward layer parameters.
data FCP i o = FCP { _fcBias    :: !(R o)
                   , _fcWeights :: !(L o i)
                   }
  deriving Generic

fcWeights
    :: Functor f
    => (L o i -> f (L o k))
    -> FCP i o
    -> f (FCP k o)
fcWeights f fcp = (\w -> fcp { _fcWeights = w }) <$> f (_fcWeights fcp)

fcBias
    :: Functor f
    => (R o -> f (R o))
    -> FCP i o
    -> f (FCP i o)
fcBias f fcp = (\b -> fcp { _fcBias = b }) <$> f (_fcBias fcp)

instance (KnownNat i, KnownNat o) => Num (FCP i o) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance (KnownNat i, KnownNat o) => Learn (R i) (R o) (FC i o) where
    type LParamMaybe (FC i o) = 'Just (FCP i o)

    initParam (FC f) g = J_ $
        FCP <$> (vecR <$> SVS.replicateM (f g))
            <*> (vecL <$> SVS.replicateM (f g))

    runLearn _ (J_ p) = stateless $ \x ->
        (p ^^. fcWeights) #> x + (p ^^. fcBias)

-- | Fully connected recurrent layer with bias.
--
-- Parameterized by its initialization distributions, and also the function
-- to compute the new state from previous input.
data FCR (h :: Nat) (i :: Nat) (o :: Nat) =
    FCR { _fcrGen      :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
        , _fcrGenState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
        , _fcrStore    :: forall s. Reifies s W => BVar s (R o) -> BVar s (R h)
        }

-- | Fully connected feed-forward layer parameters.
data FCRP h i o = FCRP { _fcrBias         :: !(R o)
                       , _fcrInputWeights :: !(L o i)
                       , _fcrStateWeights :: !(L o h)
                       }
  deriving Generic

fcrInputWeights
    :: Functor f
    => (L o i -> f (L o i'))
    -> FCRP h i o
    -> f (FCRP h i' o)
fcrInputWeights f fcrp = (\w -> fcrp { _fcrInputWeights = w })
    <$> f (_fcrInputWeights fcrp)

fcrStateWeights
    :: Functor f
    => (L o i -> f (L o i'))
    -> FCRP h i o
    -> f (FCRP h i' o)
fcrStateWeights f fcrp = (\w -> fcrp { _fcrInputWeights = w })
    <$> f (_fcrInputWeights fcrp)

-- fcrStateWeights
--     :: Functor f
--     => (L o i -> f (L o i'))
--     -> FCRP h i o
--     -> f (FCRP h i' o)
-- fcrStateWeights f fcrp = (\w -> fcrp { _fcrInputWeights = w })
--     <$> f (_fcrInputWeights fcrp)



-- fcrBias
--     :: Functor f
--     => (R o -> f (R o))
--     -> FCP i o
--     -> f (FCP i o)
-- fcrBias f fcp = (\b -> fcp { _fcBias = b }) <$> f (_fcBias fcp)
