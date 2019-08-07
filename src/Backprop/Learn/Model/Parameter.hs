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
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Backprop.Learn.Model.Parameter (
    deParam, deParamD
  , reParam, reParamD
  , dummyParam
  ) where

import           Backprop.Learn.Model.Types
import           Control.Monad.Primitive
import           Numeric.Backprop
import qualified System.Random.MWC          as MWC

-- | Fix a part of a parameter as constant, preventing backpropagation
-- through it and not training it.
--
-- Treats a @pq@ parameter as essentialyl a @(p, q)@, witnessed through the
-- split and join functions.
--
-- Takes the fixed value of @q@, as well as a stochastic mode version with
-- fixed distribution.
deParam
    :: forall p q pq s a b. (Backprop p, Backprop q)
    => (pq -> (p, q))                   -- ^ split
    -> (p -> q -> pq)                   -- ^ join
    -> q                                -- ^ fixed param
    -> (forall m. (PrimMonad m) => MWC.Gen (PrimState m) -> m q)    -- ^ fixed stoch param
    -> Model ('Just pq) s a b
    -> Model ('Just p )  s a b
deParam spl joi q qStoch = reParam (PJust . r . fromPJust)
                                   (\g -> fmap PJust . rStoch g . fromPJust)
  where
    r :: Reifies z W => BVar z p -> BVar z pq
    r p = isoVar2 joi spl p (auto q)
    rStoch
        :: (PrimMonad m, Reifies z W)
        => MWC.Gen (PrimState m)
        -> BVar z p
        -> m (BVar z pq)
    rStoch g p = isoVar2 joi spl p . auto <$> qStoch g

-- | 'deParam', but with no special stochastic mode version.
deParamD
    :: (Backprop p, Backprop q)
    => (pq -> (p, q))                   -- ^ split
    -> (p -> q -> pq)                   -- ^ join
    -> q                                -- ^ fixed param
    -> Model ('Just pq) s a b
    -> Model ('Just p )  s a b
deParamD spl joi q = deParam spl joi q (const (pure q))

-- | Pre-applies a function to a parameter before a model sees it.
-- Essentially something like 'lmap' for parameters.
--
-- Takes a determinstic function and also a stochastic function for
-- stochastic mode.
reParam
    :: (forall z. Reifies z W => PMaybe (BVar z) q -> PMaybe (BVar z) p)
    -> (forall m z. (PrimMonad m, Reifies z W) => MWC.Gen (PrimState m) -> PMaybe (BVar z) q -> m (PMaybe (BVar z) p))
    -> Model p s a b
    -> Model q s a b
reParam r rStoch f = Model
    { runLearn      = runLearn f . r
    , runLearnStoch = \g p x s -> do
        q <- rStoch g p
        runLearnStoch f g q x s
    }

-- | 'reParam', but with no special stochastic mode function.
reParamD
    :: (forall z. Reifies z W => PMaybe (BVar z) q -> PMaybe (BVar z) p)
    -> Model p s a b
    -> Model q s a b
reParamD r = reParam r (\_ -> pure . r)

-- | Give an unparameterized model a "dummy" parameter.  Useful for usage
-- with combinators like 'Control.Category..' from that require all input
-- models to share a common parameterization.
dummyParam
    :: Model 'Nothing  s a b
    -> Model p         s a b
dummyParam = reParamD (const PNothing)
