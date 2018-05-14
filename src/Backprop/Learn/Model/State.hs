{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Backprop.Learn.Model.State (
  -- * To and from statelessness
    trainState, deState, deStateD, dummyState
  -- * Manipulate model states
  , unroll, unrollFinal
  -- * Make models recurrent
  , recurrent
  ) where

import           Backprop.Learn.Model.Types
import           Control.Monad.Primitive
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Foldable
import           Data.Type.Mayb
import           Data.Type.Tuple hiding     (T2(..), T3(..))
import           Numeric.Backprop
import qualified System.Random.MWC          as MWC

-- | Make a model stateless by converting the state to a trained parameter,
-- and dropping the modified state from the result.
--
-- One of the ways to make a model stateless for training purposes.  Useful
-- when used after 'Unroll'.  See 'DeState', as well.
--
-- Its parameters are:
--
-- *   If the input has no parameters, just the initial state.
-- *   If the input has a parameter, a 'T2' of that parameter and initial state.
trainState
    :: forall p s a b.
     ( KnownMayb p
     , KnownMayb s
     , MaybeC Backprop p
     , MaybeC Backprop s
     )
    => Model           p s           a b
    -> Model (TupMaybe p s) 'Nothing a b
trainState f = Model
    { runLearn = \ps x n_ ->
        let (p, s) = splitTupMaybe @_ @p @s (\(T2B v u) -> (v, u)) ps
        in  (second . const) n_ $ runLearn f p x s
    , runLearnStoch = \g ps x n_ ->
        let (p, s) = splitTupMaybe @_ @p @s (\(T2B v u) -> (v, u)) ps
        in  (second . const) n_ <$> runLearnStoch f g p x s
    }

-- | Make a model stateless by pre-applying a fixed state (or a stochastic
-- one with fixed stribution) and dropping the modified state from the
-- result.
--
-- One of the ways to make a model stateless for training purposes.  Useful
-- when used after 'Unroll'.  See 'TrainState', as well.
deState
    :: s
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m s)
    -> Model p ('Just s) a b
    -> Model p 'Nothing  a b
deState s sStoch f = Model
    { runLearn      = \p x n_ ->
        (second . const) n_ $ runLearn f p x (J_ (auto s))
    , runLearnStoch = \g p x n_ -> do
        s' <- sStoch g
        (second . const) n_ <$> runLearnStoch f g p x (J_ (auto s'))
    }

-- | 'deState', except the state is always the same even in stochastic
-- mode.
deStateD
    :: s
    -> Model p ('Just s) a b
    -> Model p 'Nothing  a b
deStateD s = deState s (const (pure s))

-- | Unroll a (usually) stateful model into one taking a vector of
-- sequential inputs.
--
-- Basically applies the model to every item of input and returns all of
-- the results, but propagating the state between every step.
--
-- Useful when used before 'trainState' or 'deState'.  See
-- 'unrollTrainState' and 'unrollDeState'.
--
-- Compare to 'feedbackTrace', which, instead of receiving a vector of
-- sequential inputs, receives a single input and uses its output as the
-- next input.
unroll
    :: (Traversable t, Backprop a, Backprop b, Backprop (t b))
    => Model p s    a     b
    -> Model p s (t a) (t b)
unroll f = Model
    { runLearn      = \  p xs s -> first collectVar
                                 . flip runState s
                                 . traverse (state . runLearn f p)
                                 . sequenceVar
                                 $ xs
    , runLearnStoch = \g p xs s -> (fmap . first) collectVar
                                 . flip runStateT s
                                 . traverse (StateT . runLearnStoch f g p)
                                 . sequenceVar
                                 $ xs
    }

-- | Version of 'unroll' that only keeps the "final" result, dropping all
-- of the intermediate results.
--
-- Turns a stateful model into one that runs the model repeatedly on
-- multiple inputs sequentially and outputs the final result after seeing
-- all items.
unrollFinal
    :: (Traversable t, Backprop a)
    => Model p s    a  b
    -> Model p s (t a) b
unrollFinal f = Model
    { runLearn      = \  p xs s0 ->
          foldl' (\(_, s) x -> runLearn f p x s)
                 (undefined, s0)
                 (sequenceVar xs)
    , runLearnStoch = \g p xs s0 ->
          foldlM (\(_, s) x -> runLearnStoch f g p x s)
                 (undefined, s0)
                 (sequenceVar xs)
    }

-- | Fix a part of a parameter of a model to be (a function of) the
-- /previous/ ouput of the model itself.
--
-- Essentially, takes a \( X \times Y \rightarrow Z \) into a /stateful/
-- \( X \rightarrow Z \), where the Y is given by a function of the
-- /previous output/ of the model.
--
-- Essentially makes a model "recurrent": it receives its previous output
-- as input.
--
-- See 'fcr' for an application.
recurrent
    :: forall p s ab a b c.
     ( KnownMayb s
     , MaybeC Backprop s
     , Backprop ab
     , Backprop a
     , Backprop b
     )
    => (ab -> (a, b))                           -- ^ split
    -> (a -> b -> ab)                           -- ^ join
    -> BFunc c b                                -- ^ store state
    -> Model p           s            ab c
    -> Model p (TupMaybe s ('Just b)) a  c
recurrent spl joi sto f = Model
    { runLearn = \p x sy ->
        let (s, J_ y) = splitTupMaybe @_ @s @('Just b) (\(T2B v u) -> (v, u)) sy
            xy        = isoVar2 joi spl x y
            (z, s')   = runLearn f p xy s
        in  (z, tupMaybe T2B s' (J_ (sto z)))
    , runLearnStoch = \g p x sy -> do
        let (s, J_ y) = splitTupMaybe @_ @s @('Just b) (\(T2B v u) -> (v, u)) sy
            xy        = isoVar2 joi spl x y
        (z, s') <- runLearnStoch f g p xy s
        pure (z, tupMaybe T2B s' (J_ (sto z)))
    }

-- | Give a stateless model a "dummy" state.  For now, useful for using
-- with combinators like 'deState' that require state.  However, 'deState'
-- could also be made more lenient (to accept non stateful models) in the
-- future.
dummyState
    :: Model p 'Nothing   a b
    -> Model p ('Just s) a b
dummyState f = Model
    { runLearn      = \  p x s -> (second . const) s  $ runLearn f p x N_
    , runLearnStoch = \g p x s -> (second . const) s <$> runLearnStoch f g p x N_
    }
