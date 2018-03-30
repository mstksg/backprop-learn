{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Backprop.Learn.Model.State (
  -- * Make models stateless
    TrainState(..)
  , DeState(..), dsDeterm
  -- * Manipulate model states
  , Unroll(..), UnrollTrainState, UnrollDeState
  , ReState, rsDeterm
  ) where

import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Mayb
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import qualified Data.Vector.Sized         as SV
import qualified System.Random.MWC         as MWC

-- | Unroll a (usually) stateful model into one taking a vector of
-- sequential inputs.
--
-- Basically applies the model to every item of input and returns all of
-- the results, but propagating the state between every step.
--
-- Useful when used before 'TrainState' or 'DeState'.  See
-- 'UnrollTrainState' and 'UnrollDeState'.
--
-- Compare to 'FeedbackTrace', which, instead of receiving a vector of
-- sequential inputs, receives a single input and uses its output as the
-- next input.
newtype Unroll :: Nat -> Type -> Type where
    Unroll :: { getUnroll :: l } -> Unroll n l

-- | Unroll a stateful model into a stateless one taking a vector of
-- sequential inputs and treat the initial state as a trained parameter.
--
-- @
-- instance 'Learn' a b l
--     => 'Learn' ('SV.Vector' n a) ('SV.Vector' n b) ('UnrollTrainState' n l)
--
--     type 'LParamMaybe' ('UnrollDeState' n l) = 'TupMaybe' ('LParamMaybe' l) ('LStateMaybe' l)
--     type 'LStateMaybe' ('UnrollDeState' n l) = ''Nothing'
-- @
type UnrollTrainState  n l = TrainState (Unroll n l)

-- | Unroll a stateful model into a stateless one taking a vector of
-- sequential inputs and fix the initial state.
--
-- @
-- instance 'Learn' a b l
--     => 'Learn' ('SV.Vector' n a) ('SV.Vector' n b) ('UnrollDeState' n l)
--
--     type 'LParamMaybe' ('UnrollDeState' n l) = 'LParamMaybe' l
--     type 'LStateMaybe' ('UnrollDeState' n l) = ''Nothing'
-- @
type UnrollDeState n l = DeState (LState l) (Unroll n l)

instance (Learn a b l, KnownNat n, Num a, Num b) => Learn (SV.Vector n a) (SV.Vector n b) (Unroll n l) where
    type LParamMaybe (Unroll n l) = LParamMaybe l
    type LStateMaybe (Unroll n l) = LStateMaybe l

    initParam = initParam . getUnroll
    initState = initState . getUnroll

    runLearn (Unroll l) p x s = first collectVar
                              . flip runState s
                              . traverse (state . runLearn l p)
                              . sequenceVar
                              $ x

    runLearnStoch (Unroll l) g p x s = (fmap . first) collectVar
                                     . flip runStateT s
                                     . traverse (StateT . runLearnStoch l g p)
                                     . sequenceVar
                                     $ x

-- | Make a model stateless by converting the state to a trained parameter,
-- and dropping the modified state from the result.
--
-- One of the ways to make a model stateless for training purposes.  Useful
-- when used after 'Unroll'.  See 'DeState', as well.
--
-- Its parameters are:
--
-- *   If @l@ has no parameters, just the initial state.
-- *   If @l@ has parameters, a 'T2' of the parameter and initial state.
newtype TrainState :: Type -> Type where
    TrainState :: { getTrainState :: l } -> TrainState l

instance (Learn a b l, KnownMayb (LParamMaybe l), MaybeC Num (LParamMaybe l), LStateMaybe l ~ 'Just s, Num s)
      => Learn a b (TrainState l) where
    type LParamMaybe (TrainState l) = TupMaybe (LParamMaybe l) (LStateMaybe l)
    type LStateMaybe (TrainState l) = 'Nothing

    initParam (TrainState l) g = case knownMayb @(LParamMaybe l) of
      N_   -> case knownMayb @(LStateMaybe l) of
        J_ _ -> initState l g
      J_ _ -> case knownMayb @(LStateMaybe l) of
        J_ _ -> J_ $ T2 <$> fromJ_ (initParam l g)
                        <*> fromJ_ (initState l g)

    runLearn (TrainState l) t x _ = (second . const) N_
                               . runLearn l p x
                               $ s
      where
        (p, s) = splitTupMaybe @_ @(LParamMaybe l) @(LStateMaybe l)
                   (\v -> (v ^^. t2_1, v ^^. t2_2))
                   t

    runLearnStoch (TrainState l) g t x _ = (fmap . second . const) N_
                                      . runLearnStoch l g p x
                                      $ s
      where
        (p, s) = splitTupMaybe @_ @(LParamMaybe l) @(LStateMaybe l)
                   (\v -> (v ^^. t2_1, v ^^. t2_2))
                   t

-- | Make a model stateless by pre-applying a fixed state (or a stochastic
-- one with fixed stribution) and dropping the modified state from the
-- result.
--
-- One of the ways to make a model stateless for training purposes.  Useful
-- when used after 'Unroll'.  See 'TrainState', as well.
data DeState :: Type -> Type -> Type where
    DS :: { _dsInitState      :: s
          , _dsInitStateStoch :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m s
          , _dsLearn          :: l
          }
       -> DeState s l

-- | Create a 'DeState' from a deterministic, non-stochastic initialization
-- function.
dsDeterm :: s -> l -> DeState s l
dsDeterm s = DS s (const (pure s))

instance (Learn a b l, LStateMaybe l ~ 'Just s) => Learn a b (DeState s l) where
    type LParamMaybe (DeState s l) = LParamMaybe l
    type LStateMaybe (DeState s l) = 'Nothing

    initParam = initParam . _dsLearn

    runLearn (DS s _ l) p x _ = (second . const) N_
                              . runLearn l p x
                              $ J_ (constVar s)
    runLearnStoch (DS _ gs l) g p x _ = do
      s <- constVar <$> gs g
      (y, _) <- runLearnStoch l g p x (J_ s)
      pure (y, N_)

-- | Transform the state of a model by providing functions to pre-apply and
-- post-apply before and after the original model sees the state.
--
-- I don't really know why you would ever want to do this, but it was fun
-- to write.
--
-- Note that a @'ReState' p ''Nothing'@ is essentially the same as
-- @'DeState' p@; however, defining one in terms of the other is a bit
-- inconvenient, so they are provided as separate types.
data ReState :: Type -> Maybe Type -> Type -> Type where
    RS :: { _rsInitState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m t
          , _rsTo        :: forall q. Reifies q W => BVar q s -> Mayb (BVar q) t
          , _rsFrom      :: forall q. Reifies q W => Mayb (BVar q) t -> BVar q s
          , _rsFromStoch :: forall m q. (PrimMonad m, Reifies q W) => MWC.Gen (PrimState m) -> Mayb (BVar q) t -> m (BVar q s)
          , _rsLearn     :: l
          }
       -> ReState s t l

instance (Learn a b l, LStateMaybe l ~ 'Just s) => Learn a b (ReState s t l) where
    type LParamMaybe (ReState s t l) = LParamMaybe l
    type LStateMaybe (ReState s t l) = t

    initParam = initParam . _rsLearn
    initState = _rsInitState

    runLearn (RS _ f g _ l) p x = second (f . fromJ_)
                                . runLearn l p x
                                . J_
                                . g
    runLearnStoch (RS _ f _ g l) gen p x t = do
      s <- g gen t
      second (f . fromJ_) <$> runLearnStoch l gen p x (J_ s)

-- | Create a 'ReState' from a deterministic, non-stochastic
-- transformation function.
rsDeterm
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m t)
    -> (forall q. Reifies q W => BVar q s -> Mayb (BVar q) t)
    -> (forall q. Reifies q W => Mayb (BVar q) t -> BVar q s)
    -> l
    -> ReState s t l
rsDeterm i t f = RS i t f (const (pure . f))

