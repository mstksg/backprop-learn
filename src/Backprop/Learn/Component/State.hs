{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Backprop.Learn.Component.State (
    DeState(..)
  , FixState(..)
  , Unroll(..), UnrollDeState, UnrollFixState
  ) where

import           Backprop.Learn.Class
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Mayb
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import qualified Data.Vector.Sized         as SV

-- | Unroll a stateful model into one taking a vector of sequential inputs.
--
-- Useful when used before 'DeState' or 'FixState'.  See 'UnrollDeState'
-- and 'UnrollFixState'.
newtype Unroll :: Nat -> Type -> Type where
    Unroll :: { getUnroll :: l } -> Unroll n l

-- | Unroll a stateful model into a stateless one taking a vector of
-- sequential inputs and treat the initial state as a trained parameter.
--
-- @
-- instance 'Learn' a b l
--     => 'Learn' ('SV.Vector' n a) ('SV.Vector' n b) ('UnrollDeState' n l)'
--
--     type 'LParamMaybe' ('UnrollFixState' n l) = 'TupMaybe ('LParamMaybe' l) ('LStateMaybe' l)
--     type 'LStateMaybe' ('UnrollFixState' n l) = ''Nothing'
-- @
type UnrollDeState  n l = DeState (Unroll n l)

-- | Unroll a stateful model into a stateless one taking a vector of
-- sequential inputs and fix the initial state.
--
-- @
-- instance 'Learn' a b l
--     => 'Learn' ('SV.Vector' n a) ('SV.Vector' n b) ('UnrollFixState' n l)'
--
--     type 'LParamMaybe' ('UnrollFixState' n l) = 'LParamMaybe' l
--     type 'LStateMaybe' ('UnrollFixState' n l) = ''Nothing'
-- @
type UnrollFixState n l = FixState (LState l) (Unroll n l)

instance (Learn a b l, KnownNat n, Num a, Num b) => Learn (SV.Vector n a) (SV.Vector n b) (Unroll n l) where
    type LParamMaybe (Unroll n l) = LParamMaybe l
    type LStateMaybe (Unroll n l) = LStateMaybe l

    initParam (Unroll l) = initParam l
    initState (Unroll l) = initState l

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
-- when used after 'Unroll'.  See 'FixState', as well.
--
-- Its parameters are:
--
-- *   If @l@ has no parameters, just the initial state.
-- *   If @l@ has parameters, a 'T2' of the parameter and initial state.
newtype DeState :: Type -> Type where
    DeState :: { getDestate :: l } -> DeState l

instance (Learn a b l, KnownMayb (LParamMaybe l), MaybeC Num (LParamMaybe l), LStateMaybe l ~ 'Just s, Num s)
      => Learn a b (DeState l) where
    type LParamMaybe (DeState l) = TupMaybe (LParamMaybe l) (LStateMaybe l)
    type LStateMaybe (DeState l) = 'Nothing

    initParam (DeState l) g = case knownMayb @(LParamMaybe l) of
      N_   -> case knownMayb @(LStateMaybe l) of
        J_ _ -> initState l g
      J_ _ -> case knownMayb @(LStateMaybe l) of
        J_ _ -> J_ $ T2 <$> fromJ_ (initParam l g)
                        <*> fromJ_ (initState l g)

    runLearn (DeState l) t x _ = (second . const) N_
                               . runLearn l p x
                               $ s
      where
        (p, s) = splitTupMaybe @_ @(LParamMaybe l) @(LStateMaybe l)
                   (\v -> (v ^^. t2_1, v ^^. t2_2))
                   t

    runLearnStoch (DeState l) g t x _ = (fmap . second . const) N_
                                      . runLearnStoch l g p x
                                      $ s
      where
        (p, s) = splitTupMaybe @_ @(LParamMaybe l) @(LStateMaybe l)
                   (\v -> (v ^^. t2_1, v ^^. t2_2))
                   t

-- | Make a model stateless by pre-applying a fixed state and dropping the
-- modified state from the result.
--
-- One of the ways to make a model stateless for training purposes.  Useful
-- when used after 'Unroll'.  See 'DeState', as well.
data FixState :: Type -> Type -> Type where
    FS :: { _fsInitState :: s
          , _fsLearn     :: l
          }
       -> FixState s l

instance (Learn a b l, LStateMaybe l ~ 'Just s) => Learn a b (FixState s l) where
    type LParamMaybe (FixState s l) = LParamMaybe l
    type LStateMaybe (FixState s l) = 'Nothing

    initParam (FS _ l) = initParam l

    runLearn (FS s l) p x _ = (second . const) N_
                            . runLearn l p x
                            $ J_ (constVar s)
    runLearnStoch (FS s l) g p x _ = (fmap . second . const) N_
                                   . runLearnStoch l g p x
                                   $ J_ (constVar s)
