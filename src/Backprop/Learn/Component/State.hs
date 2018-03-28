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
import           Data.Type.Combinator
import           Data.Type.Mayb
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Type.Class.Higher
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
type UnrollDeState  n l = DeState                  (Unroll n l)

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
type UnrollFixState n l = FixState (LParamMaybe l) (Unroll n l)

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
-- *   If @l@ has no parameter or state, nothing.
-- *   If @l@ has parameters but no state, just the original parameters.
-- *   If @l@ has no parameters but state, just the initial state.
-- *   If @l@ has parameters and state, a 'T2' of the parameter and initial state.
--
-- However, this is really only meant to be used with types that have
-- state.  If used with a type with no state, this is essentially
-- a no-op/identity.
newtype DeState :: Type -> Type where
    DeState :: { getDestate :: l } -> DeState l

instance (Learn a b l, KnownMayb (LParamMaybe l), KnownMayb (LStateMaybe l), MaybeC Num (LParamMaybe l), MaybeC Num (LStateMaybe l))
      => Learn a b (DeState l) where
    type LParamMaybe (DeState l) = TupMaybe (LParamMaybe l) (LStateMaybe l)
    type LStateMaybe (DeState l) = 'Nothing

    initParam (DeState l) g = case knownMayb @(LParamMaybe l) of
      N_   -> case knownMayb @(LStateMaybe l) of
        N_   -> N_
        J_ _ -> initState l g
      J_ _ -> case knownMayb @(LStateMaybe l) of
        N_   -> initParam l g
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
--
-- If used with a type with no state, is essentially a no-op/identity.
data FixState :: Maybe Type -> Type -> Type where
    FS :: { _fsLearn     :: l
          , _fsInitState :: Mayb I s
          }
       -> FixState s l

instance (Learn a b l, LStateMaybe l ~ s) => Learn a b (FixState s l) where
    type LParamMaybe (FixState s l) = LParamMaybe l
    type LStateMaybe (FixState s l) = 'Nothing

    initParam (FS l _) = initParam l

    runLearn (FS l s) p x _ = (second . const) N_
                              . runLearn l p x
                              . map1 (constVar . getI)
                              $ s
    runLearnStoch (FS l s) g p x _ = (fmap . second . const) N_
                                   . runLearnStoch l g p x
                                   . map1 (constVar . getI)
                                   $ s
