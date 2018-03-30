{-# LANGUAGE DeriveGeneric                            #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE MultiParamTypeClasses                    #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeFamilies                             #-}
{-# LANGUAGE TypeInType                               #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

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
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double)
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
            , _armaGenYHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            , _armaGenEHist :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m Double
            }
         -> ARMA p q


-- data AR :: Nat -> Type where
--     AR :: { _arGenPhi   :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite p -> m Double
--           , _arGenHist  :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite n -> m Double
--           , _arVariance :: Double
--           }
--        -> AR p

-- data ARP :: Nat -> Type where
--     ARP { _arPhi :: R p
--         , _arPhi
--         }

-- data AR :: Nat -> Nat -> Type where
--     AR :: { _arGenPhi   :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite n -> Finite p -> m Double
--           , _arGenHist  :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Finite p -> Finite n -> m Double
--           , _arVariance :: Double
--           }
--        -> AR n p

-- instance (KnownNat n, KnownNat p) => Learn (R n) (R n) (AR n p) where
--     type LParamMaybe (AR n p) = 'Just (L n p)
--     type LStateMaybe (AR n p) = 'Just (L p n)
--     initParam AR{..} g = J_ $
--        vecL <$> SVS.generateM (uncurry (_arGenPhi  g) . separateProduct)
--     initState AR{..} g = J_ $
--        vecL <$> SVS.generateM (uncurry (_arGenHist g) . separateProduct)
--     runLearn AR{..} (J_ p) x (J_ s) = (y, s')
--       where
--         y  = constVar _arConstant + _ (p <> s)
--         s' = undefined

-- data ARMA :: Nat -> Type -> Type -> Type where
--     ARMA :: ARMA n p q

-- instance Learn (R n) (R n) (ARMA n p q) where

---- | @ARMA p q n m@ is a multivariate ARMA(p,q) model over an n-valued time
---- series, predicting a new m-valued time series.
----
---- In theory, the input time series should be "white noise".
--data ARMA :: Nat -> Nat -> Nat -> Nat -> Type where
--    ARMA :: { _armaGenPhi   :: forall f. PrimMonad f => MWC.Gen (PrimState f) -> Finite m -> Finite p -> f Double
--            , _armaGenTheta :: forall f. PrimMonad f => MWC.Gen (PrimState f) -> Finite n -> Finite q -> f Double
--            , _armaGenOut   :: forall f. PrimMonad f => MWC.Gen (PrimState f) -> Finite p -> Finite m -> f Double
--            , _armaGenInp   :: forall f. PrimMonad f => MWC.Gen (PrimState f) -> Finite q -> Finite n -> f Double
--            , _armaConstant :: R m
--            }
--         -> ARMA p q n m

--data ARMAP :: Nat -> Nat -> Nat -> Nat -> Type where
--    ARMAP :: { _armaPhi    :: L m p
--             , _armaTheta  :: L n q
--             -- , _armaTheta0 :: L m n
--             }
--          -> ARMAP p q n m
--  deriving Generic

--data ARMAS :: Nat -> Nat -> Nat -> Nat -> Type where
--    ARMAS :: { _armaOutHist :: L p m
--             , _armaInpHist :: L q n
--             }
--          -> ARMAS p q n m
--  deriving Generic

--instance (KnownNat n, KnownNat m, KnownNat p, KnownNat q) => Learn (R n) (R m) (ARMA p q n m) where
--    type LParamMaybe (ARMA p q n m) = 'Just (ARMAP p q n m)
--    type LStateMaybe (ARMA p q n m) = 'Just (ARMAS p q n m)

--    -- TODO: check if separateProduct works properly with vecL
--    initParam ARMA{..} g = J_ $
--        ARMAP <$> (vecL <$> SVS.generateM (uncurry (_armaGenPhi   g) . separateProduct))
--              <*> (vecL <$> SVS.generateM (uncurry (_armaGenTheta g) . separateProduct))

--    initState ARMA{..} g = J_ $
--        ARMAS <$> (vecL <$> SVS.generateM (uncurry (_armaGenOut   g) . separateProduct))
--              <*> (vecL <$> SVS.generateM (uncurry (_armaGenInp   g) . separateProduct))

--    runLearn ARMA{..} (J_ p) x (J_ s) = (y, s')
--      where
--        y  = _armaConstant + _
--        s' = s
