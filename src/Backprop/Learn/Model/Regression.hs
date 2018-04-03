{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Regression (
    Linear, linearRegression
  , Logistic, logisticRegression
  , ARMA(..), ARMAp(..), ARMAs(..)
  , ARMAUnroll, armaUnroll
  ) where

import           Backprop.Learn.Model
import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Neural
import           Backprop.Learn.Model.Parameter
import           Backprop.Learn.Model.State
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           Data.Proxy
import           Data.Type.Equality
import           GHC.Generics                          (Generic)
import           GHC.TypeLits.Compare
import           GHC.TypeLits.Extra
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update hiding            ((<.>))
import qualified Data.Vector.Sized                     as SV
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Numeric.LinearAlgebra.Static          as HS
import qualified System.Random.MWC                     as MWC

-- | Multivariate linear regression, from an n-vector to an m-vector.
--
-- Is essentially just a fully connected neural network layer with bias,
-- with no activation function.
type Linear n m = FC n m

-- | Construct a linear regression model from an initialization function
-- for coefficients
linearRegression
    :: (forall f. PrimMonad f => MWC.Gen (PrimState f) -> f Double)
    -> Linear n m
linearRegression = FC

--  | Logistic regression, from an n-vector to a single class value (0 or
--  1).
--
--  Essentially a linear regression postcomposed with the logistic
--  function.
type Logistic n = RMap (R 1) Double (Linear n 1)

-- | Construct a logistic regression model from an initialization function
-- for coefficients.
logisticRegression
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> Logistic n
logisticRegression f = RM (logistic . fst . headTail) (FC f)

-- | Auto-regressive moving average model.
--
-- ARMA(p,q) is an ARMA model with p autoregressive history terms and
-- q error (innovation) history terms.
--
-- It is a @'Learn' Double Double@ instance, and is meant to predict the
-- "next step" of a time sequence.
--
-- In this state, it is a runnable stateful model.  To train, use with
-- 'ARMAUnroll' to unroll and fix the initial state.
data ARMA :: Nat -> Nat -> Type where
    ARMA :: { _armaGenPhi   :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite p -> m Double
            , _armaGenTheta :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite q -> m Double
            , _armaGenConst :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            , _armaGenYHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            , _armaGenEHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            }
         -> ARMA p q

-- | The "unrolled" and "destated" 'ARMA' model, which takes a vector of
-- sequential inputs and outputs a vector of the model's expected next
-- steps.
--
-- Useful for actually training 'ARMA' using gradient descent.
--
-- This /fixes/ the initial error history to be zero (or a fixed stochastic
-- sample), and treats the initial output history to be a /learned
-- parameter/.
--
-- @
-- instance 'Learn' 'Double' Double ('ARMAUnroll' p q) where
--     -- | Initial state is a parameter, but initial error history is fixed
--     type 'LParamMaybe' (ARMAUnroll p q) = 'Just (T2 (ARMAp p q) (ARMAs p q))
--     type 'LStateMaybe' (ARMAUnroll p q) = 'Nothing
-- @
type ARMAUnroll p q = DeParamAt (ARMAs p q)
                                (R q)
                                (UnrollTrainState (Max p q) (ARMA p q))

-- | Constructor for 'ARMAUnroll'
armaUnroll
    :: KnownNat q
    => ARMA p q
    -> ARMAUnroll p q
armaUnroll a@ARMA{..} = DPA
    { _dpaParam      = 0
    , _dpaParamStoch = fmap vecR . SVS.replicateM . _armaGenEHist
    , _dpaLens       = armaEHist
    , _dpaLearn      = UnrollTrainState a
    }

-- | 'ARMA' parmaeters
data ARMAp :: Nat -> Nat -> Type where
    ARMAp :: { _armaPhi      :: !(R p)
             , _armaTheta    :: !(R q)
             , _armaConstant :: !Double
             }
          -> ARMAp p q
  deriving Generic

-- | 'ARMA' state
data ARMAs :: Nat -> Nat -> Type where
    ARMAs :: { _armaYPred :: !Double
             , _armaYHist :: !(R p)
             , _armaEHist :: !(R q)
             }
          -> ARMAs p q
  deriving Generic

instance (KnownNat p, KnownNat q, 1 <= p, 1 <= q) => Learn Double Double (ARMA p q) where
    type LParamMaybe (ARMA p q) = 'Just (ARMAp p q)
    type LStateMaybe (ARMA p q) = 'Just (ARMAs p q)

    initParam ARMA{..} g = J_ $
        ARMAp <$> (vecR <$> SVS.generateM (_armaGenPhi   g))
              <*> (vecR <$> SVS.generateM (_armaGenTheta g))
              <*> _armaGenConst g
    initState ARMA{..} g = J_ $
        ARMAs <$> _armaGenYHist g
              <*> (vecR <$> SVS.replicateM (_armaGenYHist g))
              <*> (vecR <$> SVS.replicateM (_armaGenEHist g))

    runLearn ARMA{..} (J_ p) x (J_ s) = (y, J_ s')
      where
        e  = x - (s ^^. armaYPred)
        y  = (p ^^. armaConstant)
           + (p ^^. armaPhi  ) <.> (s ^^. armaYHist)
           + (p ^^. armaTheta) <.> (s ^^. armaEHist)
        yHist' = case Proxy @1 %<=? Proxy @p of
          LE Refl -> single y # constVar dropLast #> (s ^^. armaYHist)
          NLE _ _ -> 0
        eHist' = case Proxy @1 %<=? Proxy @q of
          LE Refl -> single e # constVar dropLast #> (s ^^. armaEHist)
          NLE _ _ -> 0
        s' = isoVar3 ARMAs (\(ARMAs pr yh eh) -> (pr,yh,eh))
                y
                yHist'
                eHist'

dropLast :: forall n. (KnownNat n, 1 <= n) => L (n - 1) n
dropLast = HS.diagR 0 (1 :: R (n - 1))

single :: Reifies s W => BVar s Double -> BVar s (R 1)
single = vector . SV.singleton

instance Num (ARMAp p q) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance Num (ARMAs p q) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance Fractional (ARMAp p q) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance Fractional (ARMAs p q) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance Floating (ARMAp p q) where
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

instance Floating (ARMAs p q) where
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

instance Additive (ARMAp p q) where
    (.+.)   = gAdd
    addZero = gAddZero
instance Additive (ARMAs p q) where
    (.+.)   = gAdd
    addZero = gAddZero

instance (KnownNat p, KnownNat q) => Scaling Double (ARMAp p q)
instance (KnownNat p, KnownNat q) => Scaling Double (ARMAs p q)

instance (KnownNat p, KnownNat q) => Metric  Double (ARMAp p q)
instance (KnownNat p, KnownNat q) => Metric  Double (ARMAs p q)

instance (KnownNat p, KnownNat q, Ref m (ARMAp p q) v) => AdditiveInPlace m v (ARMAp p q)
instance (KnownNat p, KnownNat q, Ref m (ARMAs p q) v) => AdditiveInPlace m v (ARMAs p q)

instance (KnownNat p, KnownNat q, Ref m (ARMAp p q) v) => ScalingInPlace m v Double (ARMAp p q)
instance (KnownNat p, KnownNat q, Ref m (ARMAs p q) v) => ScalingInPlace m v Double (ARMAs p q)

armaPhi :: Lens (ARMAp p q) (ARMAp p' q) (R p) (R p')
armaPhi f a = (\x' -> a { _armaPhi = x' } ) <$> f (_armaPhi a)

armaTheta :: Lens (ARMAp p q) (ARMAp p q') (R q) (R q')
armaTheta f a = (\x' -> a { _armaTheta = x' } ) <$> f (_armaTheta a)

armaConstant :: Lens' (ARMAp p q) Double
armaConstant f a = (\x' -> a { _armaConstant = x' } ) <$> f (_armaConstant a)

armaYPred :: Lens' (ARMAs p q) Double
armaYPred f a = (\x' -> a { _armaYPred = x' } ) <$> f (_armaYPred a)

armaYHist :: Lens (ARMAs p q) (ARMAs p' q) (R p) (R p')
armaYHist f a = (\x' -> a { _armaYHist = x' } ) <$> f (_armaYHist a)

armaEHist :: Lens (ARMAs p q) (ARMAs p q') (R q) (R q')
armaEHist f a = (\x' -> a { _armaEHist = x' } ) <$> f (_armaEHist a)

