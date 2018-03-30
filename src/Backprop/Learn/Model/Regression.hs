-- {-# LANGUAGE DeriveGeneric                            #-}
-- {-# LANGUAGE GADTs                                    #-}
-- {-# LANGUAGE KindSignatures                           #-}
-- {-# LANGUAGE MultiParamTypeClasses                    #-}
-- {-# LANGUAGE RankNTypes                               #-}
-- {-# LANGUAGE RecordWildCards                          #-}
-- {-# LANGUAGE TypeApplications                         #-}
-- {-# LANGUAGE TypeFamilies                             #-}
-- {-# LANGUAGE TypeInType                               #-}
-- {-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

module Backprop.Learn.Model.Regression (
  ) where

import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Data.Finite
import           Data.Kind
import           GHC.Generics                          (Generic)
import           GHC.TypeLits.Extra
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import qualified Data.Vector.Storable.Sized            as SVS
import qualified System.Random.MWC                     as MWC

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
