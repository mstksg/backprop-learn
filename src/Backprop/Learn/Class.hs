{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TypeFamilies           #-}

module Backprop.Learn.Class (
    Learn(..)
  , NoParam, pattern NoParam
  ) where

import           Control.Monad.Primitive
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import qualified System.Random.MWC       as MWC

-- | Useful convenience type for trained models without learnable
-- parameters.  Can be used to automatically derive 'initParam' if given
-- as a model's parmaeters.
type NoParam = T0

pattern NoParam :: NoParam
pattern NoParam = T0

-- | Class for models that can be trained using gradient descent.
--
-- An instance @l@ of @'Learn' p a b@ is parameterized by @p@, takes @a@ as
-- input, and returns @b@ as outputs.
--
-- @l@ can be thought of as representing the /hyperparameters/ of the
-- model, with @p@ representing the /trained parameters/ of the model.
--
-- If no trained parameters exist, 'NoParam' can be used.  This will
-- automatically derive 'initParam'.
class (Num p, Num a, Num b) => Learn p a b l | l -> p, l -> a, l -> b where
    -- | Initialization of trainiable model parameters.
    initParam
        :: PrimMonad m
        => l
        -> MWC.Gen (PrimState m)
        -> m p

    default initParam
        :: (PrimMonad m, p ~ NoParam)
        => l
        -> MWC.Gen (PrimState m)
        -> m p
    initParam _ _ = pure T0

    -- | Run the model.
    runFixed
        :: Reifies s W
        => l
        -> BVar s p
        -> BVar s a
        -> BVar s b

    -- | Running the model in "stochastic" mode.
    --
    -- For nonstochastic models, is automatically defined in terms of
    -- 'runFixed'.
    runStoch
        :: (PrimMonad m, Reifies s W)
        => l
        -> MWC.Gen (PrimState m)
        -> BVar s p
        -> BVar s a
        -> m (BVar s b)
    runStoch l _ x = pure . runFixed l x
