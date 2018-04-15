{-# LANGUAGE AllowAmbiguousTypes                      #-}
{-# LANGUAGE DeriveDataTypeable                       #-}
{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE FlexibleInstances                        #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE PatternSynonyms                          #-}
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
    LinReg(..)
  , LogReg, pattern LogReg
  , LRp(..), lrBeta, lrAlpha, runLRp
  , ARIMA(..), ARIMAp(..), ARIMAs(..)
  , ARIMAUnroll, arimaUnroll
  , ARIMAUnrollFinal, arimaUnrollFinal
  , AR, MA, ARMA
  ) where

import           Backprop.Learn.Initialize
import           Backprop.Learn.Model.Class
import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Parameter
import           Backprop.Learn.Model.State
import           Control.DeepSeq
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           Data.List
import           Data.Maybe
import           Data.Proxy
import           Data.Type.Equality
import           Data.Typeable
import           GHC.Generics                          (Generic)
import           GHC.TypeLits.Compare
import           GHC.TypeLits.Extra
import           GHC.TypeNats
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update hiding            ((<.>))
import           Unsafe.Coerce
import qualified Data.Binary                           as Bi
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Numeric.LinearAlgebra                 as HU
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

-- | Multivariate linear regression, from an i-vector to an o-vector.
data LinReg (i :: Nat) (o :: Nat) = LinReg
  deriving Typeable

-- | Mutivariate Logistic regression, from an i-vector to an o-vector.
--
-- Essentially a linear regression postcomposed with the logistic
-- function.
type LogReg i o = RMap (R o) (R o) (LinReg i o)

-- | Constructor for a 'LogReg'
pattern LogReg :: LogReg i o
pattern LogReg <- RM _ LinReg
  where
    LogReg = RM logistic LinReg
{-# COMPLETE LogReg #-}

-- | Linear Regression parameter
data LRp i o = LRp
    { _lrAlpha :: !(R o)
    , _lrBeta  :: !(L o i)
    }
  deriving (Generic, Typeable, Show)

instance NFData (LRp i o)
instance (KnownNat i, KnownNat o) => Initialize (LRp i o)
instance (KnownNat i, KnownNat o) => Additive (LRp i o)
instance (KnownNat i, KnownNat o) => Scaling Double (LRp i o)
instance (KnownNat i, KnownNat o) => Metric Double (LRp i o)
instance (KnownNat i, KnownNat o, Ref m (LRp i o) v) => AdditiveInPlace m v (LRp i o)
instance (KnownNat i, KnownNat o, Ref m (LRp i o) v) => ScalingInPlace m v Double (LRp i o)
instance (KnownNat i, KnownNat o) => Bi.Binary (LRp i o)

lrBeta :: Lens (LRp i o) (LRp i' o) (L o i) (L o i')
lrBeta f lrp = (\w -> lrp { _lrBeta = w }) <$> f (_lrBeta lrp)

lrAlpha :: Lens' (LRp i o) (R o)
lrAlpha f lrp = (\b -> lrp { _lrAlpha = b }) <$> f (_lrAlpha lrp)

runLRp
    :: (KnownNat i, KnownNat o, Reifies s W)
    => BVar s (LRp i o)
    -> BVar s (R i)
    -> BVar s (R o)
runLRp lrp x = (lrp ^^. lrBeta) #> x + (lrp ^^. lrAlpha)

instance (KnownNat i, KnownNat o) => Num (LRp i o) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance (KnownNat i, KnownNat o) => Fractional (LRp i o) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance (KnownNat i, KnownNat o) => Floating (LRp i o) where
    pi    = gPi
    sqrt  = gSqrt
    exp   = gExp
    log   = gLog
    sin   = gSin
    cos   = gCos
    tan   = gTan
    asin  = gAsin
    acos  = gAcos
    atan  = gAtan
    sinh  = gSinh
    cosh  = gCosh
    asinh = gAsinh
    acosh = gAcosh
    atanh = gAtanh

instance (KnownNat i, KnownNat o) => Learn (R i) (R o) (LinReg i o) where
    type LParamMaybe (LinReg i o) = 'Just (LRp i o)

    runLearn _ (J_ p) = stateless (runLRp p)

-- | Auto-regressive integrated moving average model.
--
-- ARIMA(p,d,q) is an ARIMA model with p autoregressive history terms on
-- the d-th order differenced history and q error (innovation) history
-- terms.
--
-- It is a @'Learn' Double Double@ instance, and is meant to predict the
-- "next step" of a time sequence.
--
-- In this state, it is a runnable stateful model.  To train, use with
-- 'ARIMAUnroll' to unroll and fix the initial state.
data ARIMA :: Nat -> Nat -> Nat -> Type where
    ARIMA :: { _arimaGenYHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
             , _arimaGenEHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
             }
          -> ARIMA p d q

-- | The "unrolled" and "destated" 'ARIMA' model, which takes a vector of
-- sequential inputs and outputs a vector of the model's expected next
-- steps.
--
-- Useful for actually training 'ARIMA' using gradient descent.
--
-- This /fixes/ the initial error history to be zero (or a fixed stochastic
-- sample), and treats the initial output history to be a /learned
-- parameter/.
--
-- @
-- instance 'Learn' ('SV.Vector' n 'Double') (SV.Vector n Double) ('ARIMAUnroll' p q) where
--     -- | Initial state is a parameter, but initial error history is fixed
--     type 'LParamMaybe' (ARIMAUnroll p q) = 'Just (T2 (ARIMAp p q) (ARIMAs p q))
--     type 'LStateMaybe' (ARIMAUnroll p q) = 'Nothing
-- @
type ARIMAUnroll p d q = DeParamAt (T2 (ARIMAp p q) (ARIMAs p d q))
                                   (R q)
                                   (UnrollTrainState (Max (p + d) q) (ARIMA p d q))

-- | 'ARIMAUnroll', but only looking at the final output after running the
-- model on all inputs.
--
-- @
-- instance 'Learn' ('SV.Vector' n 'Double') Double ('ARIMAUnrollFinal' p q) where
--     -- | Initial state is a parameter, but initial error history is fixed
--     type 'LParamMaybe' (ARIMAUnrollFinal p q) = 'Just (T2 (ARIMAp p q) (ARIMAs p q))
--     type 'LStateMaybe' (ARIMAUnrollFinal p q) = 'Nothing
-- @
type ARIMAUnrollFinal p d q = DeParamAt (T2 (ARIMAp p q) (ARIMAs p d q))
                                        (R q)
                                        (UnrollFinalTrainState (Max (p + d) q) (ARIMA p d q))


-- | Constructor for 'ARIMAUnroll'
arimaUnroll
    :: KnownNat q
    => ARIMA p d q
    -> ARIMAUnroll p d q
arimaUnroll a@ARIMA{..} = DPA
    { _dpaParam      = 0
    , _dpaParamStoch = fmap vecR . SVS.replicateM . _arimaGenEHist
    , _dpaLens       = t2_2 . arimaEHist
    , _dpaLearn      = UnrollTrainState a
    }

-- | Constructor for 'ARIMAUnrollFinal'
arimaUnrollFinal
    :: KnownNat q
    => ARIMA p d q
    -> ARIMAUnrollFinal p d q
arimaUnrollFinal a@ARIMA{..} = DPA
    { _dpaParam      = 0
    , _dpaParamStoch = fmap vecR . SVS.replicateM . _arimaGenEHist
    , _dpaLens       = t2_2 . arimaEHist
    , _dpaLearn      = UnrollFinalTrainState a
    }


-- | 'ARIMA' parmaeters
data ARIMAp :: Nat -> Nat -> Type where
    ARIMAp :: { _arimaPhi      :: !(R p)
              , _arimaTheta    :: !(R q)
              , _arimaConstant :: !Double
              }
           -> ARIMAp p q
  deriving (Generic, Show)

-- | 'ARIMA' state
data ARIMAs :: Nat -> Nat -> Nat -> Type where
    ARIMAs :: { _arimaYPred :: !Double
             , _arimaYHist :: !(R (p + d))
             , _arimaEHist :: !(R q)
             }
          -> ARIMAs p d q
  deriving (Generic, Show)

instance (KnownNat p, KnownNat d, KnownNat q) => Learn Double Double (ARIMA p d q) where
    type LParamMaybe (ARIMA p d q) = 'Just (ARIMAp p q)
    type LStateMaybe (ARIMA p d q) = 'Just (ARIMAs p d q)

    runLearn ARIMA{..} (J_ p) x (J_ s) = (y, J_ s')
      where
        d :: L p (p + d)
        d  = difference
        e  = x - (s ^^. arimaYPred)
        y  = (p ^^. arimaConstant)
           + (p ^^. arimaPhi  ) <.> (constVar d #> (s ^^. arimaYHist))
           + (p ^^. arimaTheta) <.> (s ^^. arimaEHist)
        yHist' = case Proxy @1 %<=? Proxy @(p + d) of
          LE Refl -> single y # constVar dropLast #> (s ^^. arimaYHist)
          NLE _ _ -> 0
        eHist' = case Proxy @1 %<=? Proxy @q of
          LE Refl -> single e # constVar dropLast #> (s ^^. arimaEHist)
          NLE _ _ -> 0
        s' = isoVar3 ARIMAs (\(ARIMAs pr yh eh) -> (pr,yh,eh))
                y
                yHist'
                eHist'

monosquare :: forall n. (n <=? (n ^ 2)) :~: 'True
monosquare = unsafeCoerce Refl

dropLast :: forall n. (KnownNat n, 1 <= n) => L (n - 1) n
dropLast = case monosquare @n of
    Refl -> vecL . SVS.generate $ \ij ->
      let i :: Finite n
          j :: Finite (n - 1)
          (i, j) = separateProduct ij
      in  if fromIntegral @_ @Int i == fromIntegral j
            then 1
            else 0

single :: Reifies s W => BVar s Double -> BVar s (R 1)
single = konst

difference'
    :: Int                  -- ^ initial
    -> Int                  -- ^ target
    -> HU.Matrix Double     -- ^ target x initial
difference' n m = foldl' go (HU.ident m) [m + 1 .. n]
  where
    go x k = x HU.<> d k
    d k = HU.build (k-1, k) $ \i j ->
        case round @_ @Int (j - i) of
          0 -> 1
          1 -> -1
          _ -> 0

difference :: forall n m. (KnownNat n, KnownNat m) => L n (n + m)
difference = fromJust . H.create $ difference' (n + m) n
  where
    n = fromIntegral $ natVal (Proxy @n)
    m = fromIntegral $ natVal (Proxy @m)

instance NFData (ARIMAp p q)
instance NFData (ARIMAs p d q)

instance Num (ARIMAp p q) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance Num (ARIMAs p d q) where
    (+)         = gPlus
    (-)         = gMinus
    (*)         = gTimes
    negate      = gNegate
    abs         = gAbs
    signum      = gSignum
    fromInteger = gFromInteger

instance Fractional (ARIMAp p q) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance Fractional (ARIMAs p d q) where
    (/)          = gDivide
    recip        = gRecip
    fromRational = gFromRational

instance Floating (ARIMAp p q) where
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

instance Floating (ARIMAs p d q) where
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

instance Additive (ARIMAp p q) where
    (.+.)   = gAdd
    addZero = gAddZero
instance Additive (ARIMAs p d q) where
    (.+.)   = gAdd
    addZero = gAddZero

instance (KnownNat p, KnownNat q) => Scaling Double (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q) => Scaling Double (ARIMAs p d q)

instance (KnownNat p, KnownNat q) => Metric  Double (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q) => Metric  Double (ARIMAs p d q)

instance (KnownNat p, KnownNat q, Ref m (ARIMAp p q) v) => AdditiveInPlace m v (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q, Ref m (ARIMAs p d q) v) => AdditiveInPlace m v (ARIMAs p d q)

instance (KnownNat p, KnownNat q, Ref m (ARIMAp p q) v) => ScalingInPlace m v Double (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q, Ref m (ARIMAs p d q) v) => ScalingInPlace m v Double (ARIMAs p d q)

instance (KnownNat p, KnownNat q) => Initialize (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q) => Initialize (ARIMAs p d q)

instance (KnownNat p, KnownNat q) => Bi.Binary (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q) => Bi.Binary (ARIMAs p d q)

arimaPhi :: Lens (ARIMAp p q) (ARIMAp p' q) (R p) (R p')
arimaPhi f a = (\x' -> a { _arimaPhi = x' } ) <$> f (_arimaPhi a)

arimaTheta :: Lens (ARIMAp p q) (ARIMAp p q') (R q) (R q')
arimaTheta f a = (\x' -> a { _arimaTheta = x' } ) <$> f (_arimaTheta a)

arimaConstant :: Lens' (ARIMAp p q) Double
arimaConstant f a = (\x' -> a { _arimaConstant = x' } ) <$> f (_arimaConstant a)

arimaYPred :: Lens' (ARIMAs p d q) Double
arimaYPred f a = (\x' -> a { _arimaYPred = x' } ) <$> f (_arimaYPred a)

arimaYHist :: Lens' (ARIMAs p d q) (R (p + d))
arimaYHist f a = (\x' -> a { _arimaYHist = x' } ) <$> f (_arimaYHist a)

arimaEHist :: Lens (ARIMAs p d q) (ARIMAs p d q') (R q) (R q')
arimaEHist f a = (\x' -> a { _arimaEHist = x' } ) <$> f (_arimaEHist a)

-- | Autoregressive model
type AR p = ARIMA p 0 0

-- | Moving average model
type MA = ARIMA 0 0

-- | Autoregressive Moving average model
type ARMA p = ARIMA p 0

