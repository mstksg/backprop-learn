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
  , LParamOf, LStateOf, NoParam, NoState
  , LParam, LState
  , stateless, statelessM
  , runLearnStateless
  , runLearnStochStateless
  , Mayb(..), fromJ_
  ) where

import           Control.Monad.Primitive
import           Data.Kind
import           Data.Type.Mayb
import           Numeric.Backprop
import           Type.Class.Known
import qualified GHC.TypeLits            as TL
import qualified System.Random.MWC       as MWC

-- | The trainable parameter type of a model.  Will be a compile-time error
-- if the model has no trainable parameters.
type LParamOf l = FromJust
    ('TL.ShowType l 'TL.:<>: 'TL.Text " has no trainable parameters")
    (LParamMaybe l)

-- | The state type of a model.  Will be a compile-time error if the model
-- has no state.
type LStateOf l = FromJust
    ('TL.ShowType l 'TL.:<>: 'TL.Text " has no trainable parameters")
    (LStateMaybe l)

-- | Constraint specifying that a given model has no trainabale parameters.
type NoParam l = LParamMaybe l ~ 'Nothing

-- | Constraint specifying that a given model has no state.
type NoState l = LStateMaybe l ~ 'Nothing

-- | Is 'N_' if there is @l@ has no trainable parameters; otherwise is 'J_'
-- with @f p@, for trainable parameter type @p@.
type LParam f l = Mayb f (LParamMaybe l)

-- | Is 'N_' if there is @l@ has no state; otherwise is 'J_' with @f
-- s@, for state type @s@.
type LState f l = Mayb f (LStateMaybe l)

-- | Class for models that can be trained using gradient descent
--
-- An instance @l@ of @'Learn' a b@ is parameterized by @p@, takes @a@ as
-- input, and returns @b@ as outputs.  @l@ can be thought of as a value
-- containing the /hyperparmaeters/ of the model.
class ( MaybeC Num (LParamMaybe l)
      , MaybeC Num (LStateMaybe l)
      , Num a
      , Num b
      , Known (Mayb P) (LParamMaybe l)
      , Known (Mayb P) (LStateMaybe l)
      )
      => Learn a b l | l -> a, l -> b where

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
    initParam
        :: PrimMonad m
        => l
        -> MWC.Gen (PrimState m)
        -> LParam m l
    default initParam
        :: (LParamMaybe l ~ 'Nothing)
        => l
        -> MWC.Gen (PrimState m)
        -> LParam m l
    initParam _ _ = N_

    -- | Initialize state, given the hyperparameters in @l@.
    initState
        :: PrimMonad m
        => l
        -> MWC.Gen (PrimState m)
        -> LState m l
    default initState
        :: (LStateMaybe l ~ 'Nothing)
        => l
        -> MWC.Gen (PrimState m)
        -> LState m l
    initState _ _ = N_

    -- | Run the model itself, deterministically.
    --
    -- If your model has no state, you can define this conveniently using
    -- 'stateless'.
    runLearn
        :: Reifies s W
        => l
        -> LParam (BVar s) l
        -> BVar s a
        -> LState (BVar s) l
        -> (BVar s b, LState (BVar s) l)

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
        -> LParam (BVar s) l
        -> BVar s a
        -> LState (BVar s) l
        -> m (BVar s b, LState (BVar s) l)
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
    -> LParam (BVar s) l
    -> BVar s a
    -> BVar s b
runLearnStateless l p = fst . flip (runLearn l p) N_

runLearnStochStateless
    :: (Learn a b l, Reifies s W, NoState l, PrimMonad m)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam (BVar s) l
    -> BVar s a
    -> m (BVar s b)
runLearnStochStateless l g p = fmap fst . flip (runLearnStoch l g p) N_

--module Backprop.Learn.Class (
--    Learn(..)
--  , NoParam, pattern NoParam
--  ) where

--import           Control.Monad.Primitive
--import           Numeric.Backprop
--import           Numeric.Backprop.Tuple
--import qualified System.Random.MWC       as MWC

---- | Useful convenience type for trained models without learnable
---- parameters.  Can be used to automatically derive 'initParam' if given
---- as a model's parmaeters.
--type NoParam = T0

--pattern NoParam :: NoParam
--pattern NoParam = T0

---- | Class for models that can be trained using gradient descent.
----
---- An instance @l@ of @'Learn' p a b@ is parameterized by @p@, takes @a@ as
---- input, and returns @b@ as outputs.
----
---- @l@ can be thought of as representing the /hyperparameters/ of the
---- model, with @p@ representing the /trained parameters/ of the model.
----
---- If no trained parameters exist, 'NoParam' can be used.  This will
---- automatically derive 'initParam'.
--class (Num p, Num a, Num b) => Learn p a b l | l -> p, l -> a, l -> b where
--    -- | Initialization of trainiable model parameters.
--    initParam
--        :: PrimMonad m
--        => l
--        -> MWC.Gen (PrimState m)
--        -> m p

--    default initParam
--        :: (PrimMonad m, p ~ NoParam)
--        => l
--        -> MWC.Gen (PrimState m)
--        -> m p
--    initParam _ _ = pure T0

--    -- | Run the model.
--    runFixed
--        :: Reifies s W
--        => l
--        -> BVar s p
--        -> BVar s a
--        -> BVar s b

--    -- | Running the model in "stochastic" mode.
--    --
--    -- For nonstochastic models, is automatically defined in terms of
--    -- 'runFixed'.
--    runStoch
--        :: (PrimMonad m, Reifies s W)
--        => l
--        -> MWC.Gen (PrimState m)
--        -> BVar s p
--        -> BVar s a
--        -> m (BVar s b)
--    runStoch l _ x = pure . runFixed l x
