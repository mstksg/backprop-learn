{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Backprop.Learn.Dropout (
    DO(..)
  ) where

import           Backprop.Learn.Class
import           Data.Bool
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import qualified Data.Vector.Storable.Sized            as SVS
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
