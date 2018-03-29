{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE UndecidableInstances  #-}

module Backprop.Learn.Component.Parameter (
    DeParam(..)
  , dpDeterm
  , ReParam
  , rpDeterm
  ) where

import           Backprop.Learn.Class
import           Control.Monad.Primitive
import           Data.Kind
import           Numeric.Backprop
import qualified System.Random.MWC       as MWC

-- | Convert a model with trainabile parameters into a model without any
-- trainable parameters.
--
-- The parameters are instead fixed (or stochastic, with a fixed
-- distribution), and the model is treated as an untrainable function.
data DeParam :: Type -> Type -> Type where
    DP :: { _dpParam      :: p
          , _dpParamStoch :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m p
          , _dpLearn      :: l
          }
       -> DeParam p l

-- | Create a 'DeParam' from a deterministic, non-stochastic parameter.
dpDeterm :: p -> l -> DeParam p l
dpDeterm p = DP p (const (pure p))

instance (Learn a b l, LParamMaybe l ~ 'Just p) => Learn a b (DeParam p l) where
    type LParamMaybe (DeParam p l) = 'Nothing
    type LStateMaybe (DeParam p l) = LStateMaybe l

    initState (DP _ _ l) = initState l
    runLearn (DP p _ l) _ = runLearn l (J_ (constVar p))
    runLearnStoch (DP _ gp l) g _ x s = do
      p <- constVar <$> gp g
      runLearnStoch l g (J_ p) x s

-- | Pre-apply a function to the parameter before the original model sees
-- it.  A @'ReParam' p q@ turns a model taking @p@ into a model taking @q@.
--
-- Note that a @'ReParam' p ''Nothing'@ is essentially the same as
-- @'DeParam' p@; however, defining one in terms of the other is a bit
-- inconvenient, so they are provided as separate types.
data ReParam :: Type -> Maybe Type -> Type -> Type where
    RP :: { _rpInitParam :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m q
          , _rpFrom      :: forall s. Reifies s W => Mayb (BVar s) q -> BVar s p
          , _rpFromStoch :: forall m s. (PrimMonad m, Reifies s W) => MWC.Gen (PrimState m) -> Mayb (BVar s) q -> m (BVar s p)
          , _rpLearn     :: l
          }
       -> ReParam p q l

instance (Learn a b l, LParamMaybe l ~ 'Just p) => Learn a b (ReParam p q l) where
    type LParamMaybe (ReParam p q l) = q
    type LStateMaybe (ReParam p q l) = LStateMaybe l

    initParam (RP i _ _ _) = i
    initState (RP _ _ _ l) = initState l

    runLearn (RP _ f _ l) q = runLearn l (J_ (f q))
    runLearnStoch (RP _ _ f l) g q x s = do
      p <- f g q
      runLearnStoch l g (J_ p) x s

-- | Create a 'ReParam' from a deterministic, non-stochastic
-- transformation function.
rpDeterm
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m q)
    -> (forall s. Reifies s W => Mayb (BVar s) q -> BVar s p)
    -> l
    -> ReParam p q l
rpDeterm i f = RP i f (const (pure . f))
