{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE DefaultSignatures       #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE FunctionalDependencies  #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE KindSignatures          #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PatternSynonyms         #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TupleSections           #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeFamilyDependencies  #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Backprop.Learn.Class (
    Learn(..)
  , LParam, LState, NoParam, NoState
  , LParam_, LState_
  , stateless, statelessM
  , runLearnStateless
  , runLearnStochStateless
  , Mayb(..), fromJ_, MaybeC, KnownMayb, knownMayb
  ) where

import           Control.Monad.Primitive
import           Data.Kind
import           Data.Type.Mayb
import           Numeric.Backprop
import qualified GHC.TypeLits            as TL
import qualified System.Random.MWC       as MWC

-- | The trainable parameter type of a model.  Will be a compile-time error
-- if the model has no trainable parameters.
type LParam l = FromJust
    ('TL.ShowType l 'TL.:<>: 'TL.Text " has no trainable parameters")
    (LParamMaybe l)

-- | The state type of a model.  Will be a compile-time error if the model
-- has no state.
type LState l = FromJust
    ('TL.ShowType l 'TL.:<>: 'TL.Text " has no trainable parameters")
    (LStateMaybe l)

-- | Constraint specifying that a given model has no trainabale parameters.
type NoParam l = LParamMaybe l ~ 'Nothing

-- | Constraint specifying that a given model has no state.
type NoState l = LStateMaybe l ~ 'Nothing

-- | Is 'N_' if there is @l@ has no trainable parameters; otherwise is 'J_'
-- with @f p@, for trainable parameter type @p@.
type LParam_ f l = Mayb f (LParamMaybe l)

-- | Is 'N_' if there is @l@ has no state; otherwise is 'J_' with @f
-- s@, for state type @s@.
type LState_ f l = Mayb f (LStateMaybe l)

-- | Class for models that can be trained using gradient descent
--
-- An instance @l@ of @'Learn' a b@ is parameterized by @p@, takes @a@ as
-- input, and returns @b@ as outputs.  @l@ can be thought of as a value
-- containing the /hyperparmaeters/ of the model.
class Learn a b l | l -> a, l -> b where

    -- | The trainable parameters of model @l@.
    --
    -- By default, is ''Nothing'.  To give a type for learned parameters @p@,
    -- use the type @''Just' p@
    type LParamMaybe l :: Maybe Type

    -- | The type of the state of model @l@.  Used for things like
    -- recurrent neural networks.
    --
    -- By default, is ''Nothing'.  To give a type for state @s@, use the
    -- type @''Just' s@.
    --
    -- Most models will not use state, training algorithms will only work
    -- if 'LStateMaybe' is ''Nothing'.  However, models that use state can
    -- be converted to models that do not using 'Unroll'; this can be done
    -- before training.
    type LStateMaybe l :: Maybe Type

    type LParamMaybe l = 'Nothing
    type LStateMaybe l = 'Nothing

    -- | Initialize parameters, given the hyperparameters in @l@.
    --
    -- Default definition provided for models with no state.
    initParam
        :: PrimMonad m
        => l
        -> MWC.Gen (PrimState m)
        -> LParam_ m l
    default initParam
        :: NoParam l
        => l
        -> MWC.Gen (PrimState m)
        -> LParam_ m l
    initParam _ _ = N_

    -- | Initialize state, given the hyperparameters in @l@.
    --
    -- Default definition provided for models with no state.
    initState
        :: PrimMonad m
        => l
        -> MWC.Gen (PrimState m)
        -> LState_ m l
    default initState
        :: NoState l
        => l
        -> MWC.Gen (PrimState m)
        -> LState_ m l
    initState _ _ = N_

    -- | Run the model itself, deterministically.
    --
    -- If your model has no state, you can define this conveniently using
    -- 'stateless'.
    runLearn
        :: Reifies s W
        => l
        -> LParam_ (BVar s) l
        -> BVar s a
        -> LState_ (BVar s) l
        -> (BVar s b, LState_ (BVar s) l)

    -- | Run a model in stochastic mode.
    --
    -- If model is inherently non-stochastic, a default implementation is
    -- given in terms of 'runLearn'.
    --
    -- If your model has no state, you can define this conveniently using
    -- 'statelessStoch'.
    runLearnStoch
        :: (Reifies s W, PrimMonad m)
        => l
        -> MWC.Gen (PrimState m)
        -> LParam_ (BVar s) l
        -> BVar s a
        -> LState_ (BVar s) l
        -> m (BVar s b, LState_ (BVar s) l)
    runLearnStoch l _ p x s = pure (runLearn l p x s)

-- | Useful for defining 'runLearn' if your model has no state.
stateless
    :: (a -> b)
    -> (a -> s -> (b, s))
stateless f x = (f x,)

-- | Useful for defining 'runLearnStoch' if your model has no state.
statelessM
    :: Functor m
    => (a -> m b)
    -> (a -> s -> m (b, s))
statelessM f x s = (, s) <$> f x

runLearnStateless
    :: (Learn a b l, Reifies s W, NoState l)
    => l
    -> LParam_ (BVar s) l
    -> BVar s a
    -> BVar s b
runLearnStateless l p = fst . flip (runLearn l p) N_

runLearnStochStateless
    :: (Learn a b l, Reifies s W, NoState l, PrimMonad m)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ (BVar s) l
    -> BVar s a
    -> m (BVar s b)
runLearnStochStateless l g p = fmap fst . flip (runLearnStoch l g p) N_
