{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeInType       #-}
{-# LANGUAGE ViewPatterns     #-}

module Backprop.Learn.Model.Types (
    Model(..), ModelFunc, ModelFuncStoch
  , pattern ModelStateless, runLearnStateless, runLearnStochStateless
  , ModelFuncStateless, ModelFuncStochStateless
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

pattern ModelStateless
    :: ModelFuncStateless p a b
    -> ModelFuncStochStateless p a b
    -> Model p 'Nothing a b
pattern ModelStateless { runLearnStateless, runLearnStochStateless } <-
    (\m -> (_runLearnStateless m, _runLearnStochStateless m)
       -> (MFS runLearnStateless, MFSS runLearnStochStateless)
    )
  where
    ModelStateless l ls = Model
      { runLearn      = \p x s   -> (l p x, s)
      , runLearnStoch = \g p x s -> (, s) <$> ls g p x
      }

_runLearnStateless :: Model p 'Nothing a b -> MFS p a b
_runLearnStateless md = MFS $ \p -> fst . flip (runLearn md p) N_

_runLearnStochStateless :: Model p 'Nothing a b -> MFSS p a b
_runLearnStochStateless md = MFSS $ \g p -> fmap fst . flip (runLearnStoch md g p) N_
