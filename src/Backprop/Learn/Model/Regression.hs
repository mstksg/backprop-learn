{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}

module Backprop.Learn.Model.Regression (
    Linear(..), linearRegression
  , Logistic(..), logisticRegression
  ) where

import           Backprop.Learn.Model
import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Neural
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           GHC.Generics                          (Generic)
import           GHC.TypeLits.Extra
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Prelude hiding                        ((<>))
import qualified Data.Vector.Storable.Sized            as SVS
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
type Logistic n = RMap (R n) (R 1) Double (Linear n 1)

-- | Construct a logistic regression model from an initialization function
-- for coefficients.
logisticRegression
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
    -> Logistic n
logisticRegression f = rM (fst . headTail) $ FC f

data ARMA :: Nat -> Nat -> Type where
    ARMA :: { _armaGenPhi   :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite p -> m Double
            , _armaGenTheta :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite p -> m Double
            , _armaGenConst :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            , _armaGenYHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            , _armaGenEHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            }
         -> ARMA p q

data ARMAp :: Nat -> Nat -> Type where
    ARMAp :: { _armaPhi      :: !(R p)
             , _armaTheta    :: !(R p)
             , _armaConstant :: Double
             }
          -> ARMAp p q

data ARMAs :: Nat -> Nat -> Type where
    ARMAs :: { _armaYHist :: !(R p)
             , _armaEHist :: !(R q)
             }
          -> ARMAs p q

instance (KnownNat p, KnownNat q) => Learn Double Double (ARMA p q) where
    type LParamMaybe (ARMA p q) = 'Just (ARMAp p q)
    type LStateMaybe (ARMA p q) = 'Just (ARMAs p q)

    initParam ARMA{..} g = J_ $
        ARMAp <$> (vecR <$> SVS.generateM (_armaGenPhi   g))
              <*> (vecR <$> SVS.generateM (_armaGenTheta g))
              <*> _armaGenConst g
    initState ARMA{..} g = J_ $
        ARMAs <$> (vecR <$> SVS.replicateM (_armaGenYHist g))
              <*> (vecR <$> SVS.replicateM (_armaGenEHist g))

