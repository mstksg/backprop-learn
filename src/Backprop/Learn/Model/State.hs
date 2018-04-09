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
  -- * Make models stateless
    TrainState(..)
  , DeState(..), dsDeterm
  -- * Manipulate model states
  -- ** Unroll
  , Unroll(..)
  , UnrollTrainState, pattern UnrollTrainState, getUnrollTrainState
  , UnrollDeState, pattern UDS, _udsInitState, _udsInitStateStoch, _udsLearn
  -- ** Unroll Final
  , UnrollFinal(..)
  , UnrollFinalTrainState, pattern UnrollFinalTrainState, getUnrollFinalTrainState
  , UnrollFinalDeState, pattern UFDS, _ufdsInitState, _ufdsInitStateStoch, _ufdsLearn
  -- ** ReState
  , ReState(..), rsDeterm
  -- * Make models recurrent
  , Recurrent(..)
  -- * Provide dummy state
  , DummyState, pattern DummyState, getDummyState
  ) where

import           Backprop.Learn.Model.Class
import           Control.Monad.Primitive
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Writer
import           Data.Typeable
import           Data.Bifunctor
import           Data.Foldable
import           Data.Kind
import           Data.Semigroup
import           Data.Tuple
import           Data.Type.Mayb
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import qualified Data.Vector.Sized          as SV
import qualified System.Random.MWC          as MWC

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
  deriving (Typeable)

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

-- | Constructor and pattern for 'UnrollTrainState'
pattern UnrollTrainState :: l -> UnrollTrainState n l
pattern UnrollTrainState { getUnrollTrainState } = TrainState (Unroll getUnrollTrainState)

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

-- | Constructor and pattern for 'UnrollDeState'
pattern UDS
    :: LState l
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m (LState l))
    -> l
    -> UnrollDeState n l
pattern UDS { _udsInitState, _udsInitStateStoch, _udsLearn } =
      DS _udsInitState _udsInitStateStoch (Unroll _udsLearn)

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

-- | Version of 'Unroll' that only keeps the "final" result, dropping all
-- of the intermediate results.
--
-- Turns a stateful model into one that runs the model repeatedly on
-- multiple inputs sequentially and outputs the final result after seeing
-- all items.
newtype UnrollFinal :: Nat -> Type -> Type where
    UnrollFinal :: { getUnrollFinal :: l } -> UnrollFinal n l
  deriving (Typeable)

-- | Unroll a stateful model into a stateless one taking a vector of
-- sequential inputs and outputting the result after seeing all of them,
-- and treat the initial state as a trained parameter.
--
-- @
-- instance 'Learn' a b l
--     => 'Learn' ('SV.Vector' n a) ('SV.Vector' n b) ('UnrollFinalTrainState' n l)
--
--     type 'LParamMaybe' ('UnrollFinalDeState' n l) = 'TupMaybe' ('LParamMaybe' l) ('LStateMaybe' l)
--     type 'LStateMaybe' ('UnrollFinalDeState' n l) = ''Nothing'
-- @
type UnrollFinalTrainState  n l = TrainState (UnrollFinal n l)

-- | Constructor and pattern for 'UnrollFinalTrainState'
pattern UnrollFinalTrainState :: l -> UnrollFinalTrainState n l
pattern UnrollFinalTrainState { getUnrollFinalTrainState } = TrainState (UnrollFinal getUnrollFinalTrainState)

-- | UnrollFinal a stateful model into a stateless one taking a vector of
-- sequential inputs and outputting the final result after seeing all of them,
-- and fix the initial state.
--
-- @
-- instance 'Learn' a b l
--     => 'Learn' ('SV.Vector' n a) ('SV.Vector' n b) ('UnrollFinalDeState' n l)
--
--     type 'LParamMaybe' ('UnrollFinalDeState' n l) = 'LParamMaybe' l
--     type 'LStateMaybe' ('UnrollFinalDeState' n l) = ''Nothing'
-- @
type UnrollFinalDeState n l = DeState (LState l) (UnrollFinal n l)

-- | Constructor and pattern for 'UnrollFinalDeState'
pattern UFDS
    :: LState l
    -> (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m (LState l))
    -> l
    -> UnrollFinalDeState n l
pattern UFDS { _ufdsInitState, _ufdsInitStateStoch, _ufdsLearn } =
      DS _ufdsInitState _ufdsInitStateStoch (UnrollFinal _ufdsLearn)

instance (Learn a b l, Num a, 1 <= n) => Learn (SV.Vector n a) b (UnrollFinal n l) where
    type LParamMaybe (UnrollFinal n l) = LParamMaybe l
    type LStateMaybe (UnrollFinal n l) = LStateMaybe l

    initParam = initParam . getUnrollFinal
    initState = initState . getUnrollFinal

    runLearn (UnrollFinal l) p xs s0 =
        foldl' (\(_, s) x -> runLearn l p x s)
               (error "runLearn (unrollFinal): n cannot be 0", s0)
               (sequenceVar xs)
    runLearnStoch (UnrollFinal l) g p xs s0 =
        fmap ( first (option (error "runLearn (UnrollFinal): n cannot be 0") getLast)
             . swap
             )
      . runWriterT
      . flip execStateT s0
      . traverse_ (\x -> StateT $ \s -> do
            (y, s') <- lift $ runLearnStoch l g p x s
            WriterT $ pure (((), s'), Option (Just (Last y)))
          )
      . sequenceVar
      $ xs

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
  deriving (Typeable)

instance ( Learn a b l
         , KnownMayb (LParamMaybe l)
         , MaybeC Num (LParamMaybe l)
         , LStateMaybe l ~ 'Just s
         , Num s
         )
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
  deriving (Typeable)

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
-- @'ReState' p '()'@ is essentially 'DeState'.
data ReState :: Type -> Type -> Type -> Type where
    RS :: { _rsInitState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m t
          , _rsTo        :: forall q. Reifies q W => BVar q s -> BVar q t
          , _rsFrom      :: forall q. Reifies q W => BVar q t -> BVar q s
          , _rsFromStoch :: forall m q. (PrimMonad m, Reifies q W) => MWC.Gen (PrimState m) -> BVar q t -> m (BVar q s)
          , _rsLearn     :: l
          }
       -> ReState s t l
  deriving (Typeable)

instance (Learn a b l, LStateMaybe l ~ 'Just s) => Learn a b (ReState s t l) where
    type LParamMaybe (ReState s t l) = LParamMaybe l
    type LStateMaybe (ReState s t l) = 'Just t

    initParam = initParam . _rsLearn
    initState = (J_ .) . _rsInitState

    runLearn RS{..} p x = second (J_ . _rsTo . fromJ_)
                        . runLearn _rsLearn p x
                        . J_
                        . _rsFrom
                        . fromJ_
    runLearnStoch RS{..} gen p x (J_ t) = do
      s <- _rsFromStoch gen t
      second (J_ . _rsTo . fromJ_) <$> runLearnStoch _rsLearn gen p x (J_ s)

-- | Create a 'ReState' from a deterministic, non-stochastic transformation
-- function.
rsDeterm
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m t)     -- ^ initialize state
    -> (forall q. Reifies q W => BVar q s -> BVar q t)             -- ^ to
    -> (forall q. Reifies q W => BVar q t -> BVar q s)             -- ^ from
    -> l                                                           -- ^ model
    -> ReState s t l
rsDeterm i t f = RS i t f (const (pure . f))

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
-- A @'Recurrent' ab a b c@ takes a model from @ab@ to @c@ and turns it
-- into a model from @a@ to @c@, with extra state @b@ generated as
-- a function of the previous input.
--
-- @
-- instance 'Learn' ab c l => Learn a c ('Recurrent' ab a b c l) where
--
--     type 'LParamMaybe' (Recurrent ab a b c l) = 'LParamMaybe' l
--     type 'LStateMaybe' (Recurrent ab a b c l) = 'TupMaybe' ('LStateMaybe' l) (''Just' b)
-- @
--
-- See 'FCR' for an application.
data Recurrent :: Type -> Type -> Type -> Type -> Type -> Type where
    Rec :: { _recInit  :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m b
           , _recSplit :: ab -> (a, b)
           , _recJoin  :: a -> b -> ab
           , _recLoop  :: forall s. Reifies s W => BVar s c -> BVar s b
           , _recLearn :: l
           }
        -> Recurrent ab a b c l
  deriving (Typeable)

-- -- TODO: RecurrentN, taking a (T2 a (Vector n b)).

instance ( Learn ab c l
         , KnownMayb (LStateMaybe l)
         , Num a, Num b, Num ab
         , MaybeC Num (LStateMaybe l))
        => Learn a c (Recurrent ab a b c l) where
    type LParamMaybe (Recurrent ab a b c l) = LParamMaybe l
    type LStateMaybe (Recurrent ab a b c l) = TupMaybe (LStateMaybe l) ('Just b)

    initParam = initParam . _recLearn
    initState Rec{..} g = case knownMayb @(LStateMaybe l) of
        N_   -> J_ $ _recInit g
        J_ _ -> J_ $ T2 <$> fromJ_ (initState _recLearn g)
                        <*> _recInit g

    runLearn Rec{..} p x msy = case knownMayb @(LStateMaybe l) of
        N_   -> let y       = fromJ_ msy
                    (y', _) = runLearn _recLearn p
                        (isoVar2 _recJoin _recSplit x y)
                        N_
                in  (y', J_ (_recLoop y'))
        J_ _ -> let sy      = fromJ_ msy
                    (y', J_ s') = runLearn _recLearn p
                        (isoVar2 _recJoin _recSplit x (sy ^^. t2_2))
                        (J_ (sy ^^. t2_1))
                in  (y', J_ . isoVar2 T2 t2Tup s' . _recLoop $ y')

    runLearnStoch Rec{..} g p x msy = case knownMayb @(LStateMaybe l) of
        N_   -> do
          let y       = fromJ_ msy
          (y', _) <- runLearnStoch _recLearn g p (isoVar2 _recJoin _recSplit x y) N_
          pure (y', J_ (_recLoop y'))
        J_ _ -> do
          let sy    = fromJ_ msy
          (y', s') <- second fromJ_
                  <$> runLearnStoch _recLearn g p
                        (isoVar2 _recJoin _recSplit x (sy ^^. t2_2))
                        (J_ (sy ^^. t2_1))
          pure (y', J_ . isoVar2 T2 t2Tup s' . _recLoop $ y')

-- | Give a stateless model a "dummy" state, the unit 'T0'.  For now,
-- useful for using with combinators like 'DeState' that require state.
-- However, 'DeState' could also be made more lenient (to accept non
-- stateful models) in the future.
--
-- @
-- instance ('Learn' a b l, 'NoState' l) => Learn a b ('DummyState' a b l) where
--     type 'LParamMaybe' ('DummyState' a b l) = 'LParamMaybe' l
--     type 'LStateMaybe' ('DummyState' a b l) = ''Just' 'T0'
-- @
type DummyState a b l = Recurrent a a T0 b l

-- | Construct a 'DummyState'
pattern DummyState :: (Learn a b l, NoState l) => l -> DummyState a b l
pattern DummyState { getDummyState } <- Rec { _recLearn = getDummyState }
  where
    DummyState l = Rec { _recInit  = const (pure T0)
                       , _recSplit = (,T0)
                       , _recJoin  = const
                       , _recLoop  = const (constVar T0)
                       , _recLearn = l
                       }
{-# COMPLETE DummyState #-}
