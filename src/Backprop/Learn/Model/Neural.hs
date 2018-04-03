{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Backprop.Learn.Model.Neural (
  -- * Fully connected
  -- ** Feed-forward
    FC(..), fc, FCp(..), fcBias, fcWeights
  -- *** With activation function
  , FCA, pattern FCA, fca, _fcaGen, _fcaActivation
  -- ** Recurrent
  , FCR(..), fcr, FCRp(..), fcrBias, fcrInputWeights, fcrStateWeights
  -- *** With activation function
  , FCRA, pattern FCRA, fcra, _fcraGen, _fcraGenState, _fcraStore, _fcraActivation
  ) where


import           Backprop.Learn.Model.Class
import           Backprop.Learn.Model.Combinator
import           Control.DeepSeq
import           Control.Monad.Primitive
import           GHC.Generics                          (Generic)
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update
import           Statistics.Distribution
import qualified Data.Vector.Storable.Sized            as SVS
import qualified System.Random.MWC                     as MWC


-- | Fully connected feed-forward layer with bias.  Parameterized by its
-- initialization distribution.
--
-- Note that this has no activation function; to use as a model with
-- activation function, chain it with an activation function using 'RMap',
-- ':.~', etc.; see 'FCA' for a convenient type synonym and constructor.
--
-- Without any activation function, this is essentially a multivariate
-- linear regression.
--
-- With the logistic function as an activation function, this is
-- essentially multivariate logistic regression. (See 'Logistic')
newtype FC (i :: Nat) (o :: Nat) =
    FC { _fcGen :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
       }

-- | Construct an @'FC' i o@ using a given distribution from the
-- /statistics/ library.
fc :: ContGen d => d -> FC i o
fc d = FC (genContVar d)

-- | Convenient synonym for an 'FC' post-composed with a simple
-- parameterless activation function.
type FCA i o = RMap (R o) (R o) (FC i o)

-- | Construct an 'FCA' using a generating function and activation
-- function.
--
-- Some common ones include 'logistic' and @'vmap' 'reLU'@.
pattern FCA
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCA i o
pattern FCA { _fcaGen, _fcaActivation } = RM _fcaActivation (FC _fcaGen)

-- | Construct an @'FCA' i o@ using a given distribution from the
-- /statistics/ library.
fca :: ContGen d
    => d
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCA i o
fca d = FCA (genContVar d)

-- | Fully connected feed-forward layer parameters.
data FCp i o = FCp { _fcBias    :: !(R o)
                   , _fcWeights :: !(L o i)
                   }
  deriving Generic

instance NFData (FCp i o)
instance (KnownNat i, KnownNat o) => Additive (FCp i o)
instance (KnownNat i, KnownNat o) => Scaling Double (FCp i o)
instance (KnownNat i, KnownNat o) => Metric Double (FCp i o)
instance (KnownNat i, KnownNat o, Ref m (FCp i o) v) => AdditiveInPlace m v (FCp i o)
instance (KnownNat i, KnownNat o, Ref m (FCp i o) v) => ScalingInPlace m v Double (FCp i o)

fcWeights :: Lens (FCp i o) (FCp i' o) (L o i) (L o i')
fcWeights f fcp = (\w -> fcp { _fcWeights = w }) <$> f (_fcWeights fcp)

fcBias :: Lens' (FCp i o) (R o)
fcBias f fcp = (\b -> fcp { _fcBias = b }) <$> f (_fcBias fcp)

instance (KnownNat i, KnownNat o) => Num (FCp i o) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance (KnownNat i, KnownNat o) => Fractional (FCp i o) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance (KnownNat i, KnownNat o) => Floating (FCp i o) where
    pi    = gPi
    sqrt  = gSqrt
    exp   = gExp
    log   = gLog
    sin   = gSin
    cos   = gCos
    asin  = gAsin
    acos  = gAcos
    atan  = gAtan
    sinh  = gSinh
    cosh  = gCosh
    asinh = gAsinh
    acosh = gAcosh
    atanh = gAtanh

instance (KnownNat i, KnownNat o) => Learn (R i) (R o) (FC i o) where
    type LParamMaybe (FC i o) = 'Just (FCp i o)

    initParam (FC f) g = J_ $
        FCp <$> (vecR <$> SVS.replicateM (f g))
            <*> (vecL <$> SVS.replicateM (f g))

    runLearn _ (J_ p) = stateless $ \x ->
        ((p ^^. fcWeights) #> x) + p ^^. fcBias

-- | Fully connected recurrent layer with bias.
--
-- Parameterized by its initialization distributions, and also the function
-- to compute the new state from previous input.
data FCR (h :: Nat) (i :: Nat) (o :: Nat) =
    FCR { _fcrGen      :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
        , _fcrGenState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
        , _fcrStore    :: forall s. Reifies s W => BVar s (R o) -> BVar s (R h)
        }

-- | Convenient synonym for an 'FCR' post-composed with a simple
-- parameterless activation function.
type FCRA h i o = RMap (R o) (R o) (FCR h i o)

-- | Construct an 'FCRA' using a generating function and activation
-- function.
--
-- Some common ones include 'logistic' and @'vmap' 'reLU'@.
pattern FCRA
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCRA h i o
pattern FCRA { _fcraGen, _fcraGenState, _fcraStore, _fcraActivation }
          = RM _fcraActivation (FCR _fcraGen _fcraGenState _fcraStore)

-- | Fully connected recurrent layer parameters.
data FCRp h i o = FCRp { _fcrBias         :: !(R o)
                       , _fcrInputWeights :: !(L o i)
                       , _fcrStateWeights :: !(L o h)
                       }
  deriving Generic

instance NFData (FCRp h i o)
instance (KnownNat h, KnownNat i, KnownNat o) => Additive (FCRp h i o)
instance (KnownNat h, KnownNat i, KnownNat o) => Scaling Double (FCRp h i o)
instance (KnownNat h, KnownNat i, KnownNat o) => Metric Double (FCRp h i o)
instance (KnownNat h, KnownNat i, KnownNat o, Ref m (FCRp h i o) v) => AdditiveInPlace m v (FCRp h i o)
instance (KnownNat h, KnownNat i, KnownNat o, Ref m (FCRp h i o) v) => ScalingInPlace m v Double (FCRp h i o)

-- | Construct an @'FCR' h i o@ using given distributions from the
-- /statistics/ library.
fcr :: (ContGen d, ContGen e)
    => d
    -> e
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> FCR h i o
fcr d e = FCR (genContVar d) (genContVar e)

-- | Construct an @'FCRA' h i o@ using given distributions from the
-- /statistics/ library.
fcra :: (ContGen d, ContGen e)
    => d
    -> e
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R h))
    -> (forall s. Reifies s W => BVar s (R o) -> BVar s (R o))
    -> FCRA h i o
fcra d e = FCRA (genContVar d) (genContVar e)

fcrInputWeights :: Lens (FCRp h i o) (FCRp h i' o) (L o i) (L o i')
fcrInputWeights f fcrp = (\w -> fcrp { _fcrInputWeights = w })
    <$> f (_fcrInputWeights fcrp)

fcrStateWeights :: Lens (FCRp h i o) (FCRp h' i o) (L o h) (L o h')
fcrStateWeights f fcrp = (\w -> fcrp { _fcrStateWeights = w })
    <$> f (_fcrStateWeights fcrp)

fcrBias :: Lens' (FCRp h i o) (R o)
fcrBias f fcrp = (\b -> fcrp { _fcrBias = b }) <$> f (_fcrBias fcrp)

instance (KnownNat h, KnownNat i, KnownNat o) => Num (FCRp h i o) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance (KnownNat h, KnownNat i, KnownNat o) => Fractional (FCRp h i o) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance (KnownNat h, KnownNat i, KnownNat o) => Floating (FCRp h i o) where
    pi    = gPi
    sqrt  = gSqrt
    exp   = gExp
    log   = gLog
    sin   = gSin
    cos   = gCos
    asin  = gAsin
    acos  = gAcos
    atan  = gAtan
    sinh  = gSinh
    cosh  = gCosh
    asinh = gAsinh
    acosh = gAcosh
    atanh = gAtanh

instance (KnownNat h, KnownNat i, KnownNat o) => Learn (R i) (R o) (FCR h i o) where
    type LParamMaybe (FCR h i o) = 'Just (FCRp h i o)
    type LStateMaybe (FCR h i o) = 'Just (R h)

    initParam (FCR f _ _) g = J_ $
        FCRp <$> (vecR <$> SVS.replicateM (f g))
             <*> (vecL <$> SVS.replicateM (f g))
             <*> (vecL <$> SVS.replicateM (f g))

    initState (FCR _ f _) = J_ . fmap vecR . SVS.replicateM . f

    runLearn (FCR _ _ s) (J_ p) x (J_ h) = (y, J_ (s y))
      where
        y  = ((p ^^. fcrInputWeights) #> x)
           + ((p ^^. fcrStateWeights) #> h)
           + p ^^. fcrBias

