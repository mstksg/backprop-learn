{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeInType       #-}
{-# LANGUAGE ViewPatterns     #-}

module Backprop.Learn.Model.Types (
    -- * Model type
    ModelFunc, ModelFuncStoch
  , Model(..)
    -- * Specialized Models
    -- ** Stateless
  , ModelFuncStateless, ModelFuncStochStateless
  , ModelStateless, pattern ModelStateless, runLearnStateless, runLearnStochStateless
    -- ** Stateless and Parameterless
  , BFunc, BFuncStoch
  , Func, pattern Func, runFunc, runFuncStoch
  ) where

import           Control.Monad.Primitive
import           Data.Kind
import           Data.Type.Mayb
import           Numeric.Backprop
import qualified System.Random.MWC       as MWC

type ModelFunc p s a b = forall z. Reifies z W
    => Mayb (BVar z) p
    -> BVar z a
    -> Mayb (BVar z) s
    -> (BVar z b, Mayb (BVar z) s)

type ModelFuncStoch p s a b = forall m z. (PrimMonad m, Reifies z W)
    => MWC.Gen (PrimState m)
    -> Mayb (BVar z) p
    -> BVar z a
    -> Mayb (BVar z) s
    -> m (BVar z b, Mayb (BVar z) s)

-- | General parameterized model with potential state
data Model :: Maybe Type -> Maybe Type -> Type -> Type -> Type where
    Model :: { runLearn      :: ModelFunc      p s a b
             , runLearnStoch :: ModelFuncStoch p s a b
             } -> Model p s a b

type ModelFuncStateless p a b = forall z. Reifies z W
    => Mayb (BVar z) p
    -> BVar z a
    -> BVar z b

type ModelFuncStochStateless p a b = forall m z. (PrimMonad m, Reifies z W)
    => MWC.Gen (PrimState m)
    -> Mayb (BVar z) p
    -> BVar z a
    -> m (BVar z b)

newtype MFS  p a b = MFS  (ModelFuncStateless      p a b)
newtype MFSS p a b = MFSS (ModelFuncStochStateless p a b)

-- | Parameterized model with no state
type ModelStateless p = Model p 'Nothing

-- | Construct a 'ModelStateless'.
pattern ModelStateless
    :: ModelFuncStateless p a b
    -> ModelFuncStochStateless p a b
    -> ModelStateless p a b
pattern ModelStateless { runLearnStateless, runLearnStochStateless } <-
    (\m -> (_runLearnStateless m, _runLearnStochStateless m)
       -> (MFS runLearnStateless, MFSS runLearnStochStateless)
    )
  where
    ModelStateless l ls = Model
      { runLearn      = \  p x s -> (l p x, s)
      , runLearnStoch = \g p x s -> (, s) <$> ls g p x
      }

_runLearnStateless :: Model p 'Nothing a b -> MFS p a b
_runLearnStateless md = MFS $ \p x -> fst $ runLearn md p x N_

_runLearnStochStateless :: Model p 'Nothing a b -> MFSS p a b
_runLearnStochStateless md = MFSS $ \g p x -> fst <$> runLearnStoch md g p x N_

type BFunc a b = forall z. Reifies z W
    => BVar z a
    -> BVar z b
type BFuncStoch a b = forall m z. (PrimMonad m, Reifies z W)
    => MWC.Gen (PrimState m)
    -> BVar z a
    -> m (BVar z b)

newtype BF  a b = BF  (BFunc      a b)
newtype BFS a b = BFS (BFuncStoch a b)

type Func = Model 'Nothing 'Nothing

-- | Unparameterized model with no state
pattern Func :: BFunc a b -> BFuncStoch a b -> Func a b
pattern Func { runFunc, runFuncStoch } <-
    (\m -> (_runFunc m, _runFuncStoch m)
       -> (BF runFunc, BFS runFuncStoch)
    )
  where
    Func r rs = ModelStateless
      { runLearnStateless      = const r
      , runLearnStochStateless = const . rs
      }

_runFunc :: Model 'Nothing 'Nothing a b -> BF a b
_runFunc md = BF $ runLearnStateless md N_

_runFuncStoch :: Model 'Nothing 'Nothing a b -> BFS a b
_runFuncStoch md = BFS $ flip (runLearnStochStateless md) N_
