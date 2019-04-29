{-# LANGUAGE AllowAmbiguousTypes                      #-}
{-# LANGUAGE ApplicativeDo                            #-}
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
{-# LANGUAGE StandaloneDeriving                       #-}
{-# LANGUAGE TemplateHaskell                          #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE UndecidableInstances                     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

module Backprop.Learn.Model.Regression (
  -- * Linear Regression
    linReg, logReg
  , LRp(..), lrAlpha, lrBeta, runLRp
  -- * Reshape
  , reshapeLRpInput, reshapeLRpOutput
  , expandLRpInput, expandLRpOutput
  , premuteLRpInput, permuteLRpOutput
  -- * ARIMA
  , arima, autoregressive, movingAverage, arma
  , ARIMAp(..), ARIMAs(..)
  , arimaPhi, arimaTheta, arimaConstant, arimaYPred, arimaYHist, arimaEHist
  ) where

import           Backprop.Learn.Initialize
import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Types
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
import           GHC.TypeNats
import           Lens.Micro.TH
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.OneLiner
import           Numeric.Opto.Ref
import           Numeric.Opto.Update hiding            ((<.>))
import           Statistics.Distribution
import           Unsafe.Coerce
import qualified Data.Binary                           as Bi
import qualified Data.Vector.Generic.Sized             as SVG
import qualified Data.Vector.Sized                     as SV
import qualified Data.Vector.Storable.Sized            as SVS
import qualified Numeric.LinearAlgebra                 as HU
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

-- | Linear Regression parameter
data LRp i o = LRp
    { _lrAlpha :: !(R o)
    , _lrBeta  :: !(L o i)
    }
  deriving (Generic, Typeable, Show)

makeLenses ''LRp

instance NFData (LRp i o)
instance (KnownNat i, KnownNat o) => Initialize (LRp i o)
instance (KnownNat i, KnownNat o) => Additive (LRp i o)
instance (KnownNat i, KnownNat o) => Scaling Double (LRp i o)
instance (KnownNat i, KnownNat o) => Metric Double (LRp i o)
instance (KnownNat i, KnownNat o, Ref m (LRp i o) v) => AdditiveInPlace m v (LRp i o)
instance (KnownNat i, KnownNat o, Ref m (LRp i o) v) => ScalingInPlace m v Double (LRp i o)
instance (KnownNat i, KnownNat o) => Bi.Binary (LRp i o)
instance (KnownNat i, KnownNat o) => Backprop (LRp i o)

runLRp
    :: (KnownNat i, KnownNat o, Reifies s W)
    => BVar s (LRp i o)
    -> BVar s (R i)
    -> BVar s (R o)
runLRp lrp x = (lrp ^^. lrBeta) #> x + (lrp ^^. lrAlpha)

-- | Reshape an 'LRp' to take more or less inputs.  If more, new parameters
-- are initialized randomly according to the given distribution.
reshapeLRpInput
    :: (ContGen d, PrimMonad m, KnownNat i, KnownNat i', KnownNat o)
    => d
    -> MWC.Gen (PrimState m)
    -> LRp i o
    -> m (LRp i' o)
reshapeLRpInput d g (LRp α β) =
    LRp α <$> reshapeLCols d g β

-- | Reshape an 'LRp' to return more or less outputs  If more, new
-- parameters are initialized randomly according to the given distribution.
reshapeLRpOutput
    :: (ContGen d, PrimMonad m, KnownNat i, KnownNat o, KnownNat o')
    => d
    -> MWC.Gen (PrimState m)
    -> LRp i o
    -> m (LRp i o')
reshapeLRpOutput d g (LRp α β) =
    LRp <$> reshapeR d g α
        <*> reshapeLRows d g β

linReg
    :: (KnownNat i, KnownNat o)
    => Model ('Just (LRp i o)) 'Nothing (R i) (R o)
linReg = modelStatelessD (\(J_ p) -> runLRp p)

logReg
    :: (KnownNat i, KnownNat o)
    => Model ('Just (LRp i o)) 'Nothing (R i) (R o)
logReg = funcD logistic <~ linReg

-- | Adjust an 'LRp' to take extra inputs, initialized randomly.
--
-- Initial contributions to each output is randomized.
expandLRpInput
    :: (PrimMonad m, ContGen d, KnownNat i, KnownNat j, KnownNat o)
    => LRp i o
    -> d
    -> MWC.Gen (PrimState m)
    -> m (LRp (i + j) o)
expandLRpInput LRp{..} d g = LRp _lrAlpha . (_lrBeta H.|||) <$> initialize d g

-- | Adjust an 'LRp' to return extra ouputs, initialized randomly
expandLRpOutput
    :: (PrimMonad m, ContGen d, KnownNat i, KnownNat o, KnownNat p)
    => LRp i o
    -> d
    -> MWC.Gen (PrimState m)
    -> m (LRp i (o + p))
expandLRpOutput LRp{..} d g = do
    newAlpha <- initialize d g
    newBeta  <- initialize d g
    pure (LRp (_lrAlpha H.# newAlpha) (_lrBeta H.=== newBeta))

-- | Premute (or remove) inputs
--
-- Removed inputs will simply have their contributions removed from each
-- output.
premuteLRpInput
    :: SV.Vector i' (Finite i)
    -> LRp i o
    -> LRp i' o
premuteLRpInput is p = p { _lrBeta = colsL . fmap (β `SV.index`) $ is }
  where
    β = lCols (_lrBeta p)

-- | Premute (or remove) outputs
permuteLRpOutput
    :: SV.Vector o' (Finite o)
    -> LRp i o
    -> LRp i o'
permuteLRpOutput is LRp{..} =
    LRp { _lrAlpha = vecR . SVG.convert . fmap (α `SVS.index`) $ is
        , _lrBeta  = rowsL . fmap (β `SV.index`) $ is
        }
  where
    α = rVec _lrAlpha
    β = lRows _lrBeta

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

-- | 'ARIMA' parmaeters
data ARIMAp :: Nat -> Nat -> Type where
    ARIMAp :: { _arimaPhi      :: !(R p)
              , _arimaTheta    :: !(R q)
              , _arimaConstant :: !Double
              }
           -> ARIMAp p q
  deriving (Generic, Typeable, Show)

makeLenses ''ARIMAp

-- | 'ARIMA' state
data ARIMAs :: Nat -> Nat -> Nat -> Type where
    ARIMAs :: { _arimaYPred :: !Double
              , _arimaYHist :: !(R (p + d))
              , _arimaEHist :: !(R q)
              }
          -> ARIMAs p d q
  deriving (Generic, Typeable, Show)

makeLenses ''ARIMAs


arima
    :: forall p d q. (KnownNat p, KnownNat d, KnownNat q)
    => Model ('Just (ARIMAp p q)) ('Just (ARIMAs p d q)) Double Double
arima = modelD $ \(J_ p) x (J_ s) ->
    let d :: L p (p + d)
        d = difference
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
    in  (y, J_ s')

autoregressive
    :: KnownNat p
    => Model ('Just (ARIMAp p 0)) ('Just (ARIMAs p 0 0)) Double Double
autoregressive = arima

movingAverage
    :: KnownNat q
    => Model ('Just (ARIMAp 0 q)) ('Just (ARIMAs 0 0 q)) Double Double
movingAverage = arima

arma
    :: (KnownNat p, KnownNat q)
    => Model ('Just (ARIMAp p q)) ('Just (ARIMAs p 0 q)) Double Double
arma = arima

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

instance (KnownNat p, KnownNat q) => Backprop (ARIMAp p q)
instance (KnownNat p, KnownNat d, KnownNat q) => Backprop (ARIMAs p d q)
