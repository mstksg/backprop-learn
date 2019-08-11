{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TupleSections    #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeInType       #-}
{-# LANGUAGE ViewPatterns     #-}

module Backprop.Learn.Model.Types (
    -- * Model type
    ModelFunc, ModelFuncStoch
  , Model(..)
  , modelD
    -- * Specialized Models
    -- ** Stateless
  , ModelFuncStateless, ModelFuncStochStateless
  , ModelStateless, pattern ModelStateless, runLearnStateless, runLearnStochStateless
  , modelStatelessD
    -- ** Stateless and Parameterless
  , BFunc, BFuncStoch
  , Func, pattern Func, runFunc, runFuncStoch
  , funcD
    -- * Manipulating models as functions
  , ModelFuncM, withModelFunc0, withModelFunc, withModelFunc2
    -- * Utility
  , PMaybe(..), fromPJust, Learnables
  -- , HKD
  ) where

import           Control.Category
import           Control.Monad.Primitive
import           Control.Monad.Trans.Reader
import           Data.Functor.Identity
import           Data.Kind
import           Data.Singletons
import           Data.Type.Functor.Product
import           Data.Type.Mayb
import           Data.Type.Tuple
import           Data.Vinyl
import           Numeric.Backprop
import           Prelude hiding             ((.))
import qualified System.Random.MWC          as MWC

type ModelFunc p s a b = forall z. Reifies z W
    => PMaybe (BVar z) p
    -> BVar z a
    -> PMaybe (BVar z) s
    -> (BVar z b, PMaybe (BVar z) s)

type ModelFuncStoch p s a b = forall m z. (PrimMonad m, Reifies z W)
    => MWC.Gen (PrimState m)
    -> PMaybe (BVar z) p
    -> BVar z a
    -> PMaybe (BVar z) s
    -> m (BVar z b, PMaybe (BVar z) s)

-- | General parameterized model with potential state
data Model :: Maybe Type -> Maybe Type -> Type -> Type -> Type where
    Model :: { runLearn      :: ModelFunc      p s a b
             , runLearnStoch :: ModelFuncStoch p s a b
             } -> Model p s a b

-- | Construct a deterministic model, with no stochastic component.
modelD :: ModelFunc p s a b -> Model p s a b
modelD f = Model { runLearn      = f
                 , runLearnStoch = \_ p x -> pure . f p x
                 }

type ModelFuncStateless p a b = forall z. Reifies z W
    => PMaybe (BVar z) p
    -> BVar z a
    -> BVar z b

type ModelFuncStochStateless p a b = forall m z. (PrimMonad m, Reifies z W)
    => MWC.Gen (PrimState m)
    -> PMaybe (BVar z) p
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

-- | Construct a deterministic stateless model, with no stochastic
-- component.
modelStatelessD :: ModelFuncStateless p a b -> ModelStateless p a b
modelStatelessD f = ModelStateless
    { runLearnStateless      = f
    , runLearnStochStateless = \_ p -> pure . f p
    }

_runLearnStateless :: Model p 'Nothing a b -> MFS p a b
_runLearnStateless md = MFS $ \p x -> fst $ runLearn md p x PNothing

_runLearnStochStateless :: Model p 'Nothing a b -> MFSS p a b
_runLearnStochStateless md = MFSS $ \g p x -> fst <$> runLearnStoch md g p x PNothing

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

-- | Construct an deterministic unparameterized stateless model, with no
-- stochastic component.
funcD :: BFunc a b -> Func a b
funcD f = Func { runFunc      = f
               , runFuncStoch = const (pure . f)
               }

_runFunc :: Model 'Nothing 'Nothing a b -> BF a b
_runFunc md = BF $ runLearnStateless md PNothing

_runFuncStoch :: Model 'Nothing 'Nothing a b -> BFS a b
_runFuncStoch md = BFS $ flip (runLearnStochStateless md) PNothing

-- | Share parameter and sequence state
instance Category (Model p s) where
    id    = modelD $ \_ x s -> (x, s)
    f . g = Model
      { runLearn      = \p x s0 -> let (y, s1) = runLearn g p x s0
                                   in  runLearn f p y s1
      , runLearnStoch = \gen p x s0 -> do
          (y, s1) <- runLearnStoch g gen p x s0
          runLearnStoch f gen p y s1
      }

type ModelFuncM m p s a b = forall z. Reifies z W
    => PMaybe (BVar z) p
    -> BVar z a
    -> PMaybe (BVar z) s
    -> m (BVar z b, PMaybe (BVar z) s)

withModelFunc0
    :: (forall m. Monad m => ModelFuncM m p s a b)
    -> Model p s a b
withModelFunc0 f = Model
    { runLearn      = \p x -> runIdentity . f p x
    , runLearnStoch = \g p x -> flip runReaderT g . f p x
    }

withModelFunc
    :: (forall m. Monad m => ModelFuncM m p s a b -> ModelFuncM m q t c d)
    -> Model p s a b
    -> Model q t c d
withModelFunc f m = Model
    { runLearn      = \p x -> runIdentity . f (runLearnModelFuncM m) p x
    , runLearnStoch = \g p x -> flip runReaderT g . f (runLearnStochModelFuncM m) p x
    }

withModelFunc2
    :: (forall m. Monad m => ModelFuncM m p s a b -> ModelFuncM m q t c d -> ModelFuncM m r u e f)
    -> Model p s a b
    -> Model q t c d
    -> Model r u e f
withModelFunc2 f m n = Model
    { runLearn      = \p x ->
            runIdentity
          . f (runLearnModelFuncM m) (runLearnModelFuncM n) p x
    , runLearnStoch = \g p x ->
            flip runReaderT g
          . f (runLearnStochModelFuncM m) (runLearnStochModelFuncM n) p x
    }

runLearnModelFuncM
    :: Model p s a b
    -> ModelFuncM Identity p s a b
runLearnModelFuncM m p x = Identity . runLearn m p x

runLearnStochModelFuncM
    :: PrimMonad m
    => Model p s a b
    -> ModelFuncM (ReaderT (MWC.Gen (PrimState m)) m) p s a b
runLearnStochModelFuncM m p x s = ReaderT $ \g -> runLearnStoch m g p x s

-- | Combination of common constraints for type-level lists.
type Learnables as = ( PureProd [] as
                     , ReifyConstraint Backprop TF as
                     , RMap as
                     , RApply as
                     )

-- -- | Helper type family for HKD data types.  See
-- -- <http://reasonablypolymorphic.com/blog/higher-kinded-data>
-- type family HKD f a where
--     HKD I a = a
--     HKD f a = f a
