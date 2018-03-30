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
    DeParam(..)
  , dpDeterm
  , DeParamAt(..)
  , dpaDeterm
  , ReParam
  , rpDeterm
  ) where

import           Backprop.Learn.Model
import           Control.Monad.Primitive
import           Data.Kind
import           Lens.Micro
import           Numeric.Backprop
import qualified System.Random.MWC       as MWC

-- | Convert a model with trainabile parameters into a model without any
-- trainable parameters.
--
-- The parameters are instead fixed (or stochastic, with a fixed
-- distribution), and the model is treated as an untrainable function.
--
-- 'DeParam' is essentially 'DeParamAt', with 'id' as the lens.
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

    initState = initState . _dpLearn
    runLearn DP{..} _ = runLearn _dpLearn (J_ (constVar _dpParam))
    runLearnStoch DP{..} g _ x s = do
      p <- constVar <$> _dpParamStoch g
      runLearnStoch _dpLearn g (J_ p) x s

-- | Wrapping a mode with @'DeParamAt' p q@ will fix a specific part of the
-- parameter type @p@ to a given fixed (or stochastic with a fixed
-- distribution) value of type @q@.  That field is not backpropagated, and
-- so its gradient will always be zero.
--
-- The part is specified using a 'Lens''.  This really only makes sense if
-- @p@ is a record, and the lens points to a field (or multiple fields, to
-- a tuple) of the record.
--
-- 'DeParam' is essentially 'DeParamAt', with 'id' as the lens.
data DeParamAt :: Type -> Type -> Type -> Type where
    DPA :: { _dpaParam      :: q
           , _dpaParamStoch :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m q
           , _dpaLens       :: Lens' p q
           , _dpaLearn      :: l
           }
        -> DeParamAt p q l

-- | Create a 'DeParamAt' from a deterministic, non-stochastic fixed value
-- as a part of the parameter.
dpaDeterm :: q -> Lens' p q -> l -> DeParamAt p q l
dpaDeterm q = DPA q (const (pure q))

instance (Learn a b l, LParamMaybe l ~ 'Just p, Num p, Num q) => Learn a b (DeParamAt p q l) where
    type LParamMaybe (DeParamAt p q l) = LParamMaybe l
    type LStateMaybe (DeParamAt p q l) = LStateMaybe l

    initParam DPA{..} g = J_ $ do
        p <- fromJ_ $ initParam _dpaLearn g
        q <- _dpaParamStoch g
        pure $ p & _dpaLens .~ q
    initState = initState . _dpaLearn

    runLearn DPA{..} (J_ p) = runLearn _dpaLearn (J_ p')
      where
        p' = p & _dpaLens .~~ constVar _dpaParam

    runLearnStoch DPA{..} g (J_ p) x s = do
        q <- _dpaParamStoch g
        let p' = p & _dpaLens .~~ constVar q
        runLearnStoch _dpaLearn g (J_ p') x s


-- | Pre-apply a function to the parameter before the original model sees
-- it.  A @'ReParam' p q@ turns a model taking @p@ into a model taking @q@.
--
-- Note that a @'ReParam' p ''Nothing'@ is essentially the same as
-- a @'DeParam' p@, and one could implement @'DeParamAt' p q@ in terms of
-- @'ReParam' p (''Just' q)@.
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

    initParam = _rpInitParam
    initState = initState . _rpLearn

    runLearn RP{..} q = runLearn _rpLearn (J_ (_rpFrom q))
    runLearnStoch RP{..} g q x s = do
      p <- _rpFromStoch g q
      runLearnStoch _rpLearn g (J_ p) x s

-- | Create a 'ReParam' from a deterministic, non-stochastic
-- transformation function.
rpDeterm
    :: (forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m q)
    -> (forall s. Reifies s W => Mayb (BVar s) q -> BVar s p)
    -> l
    -> ReParam p q l
rpDeterm i f = RP i f (const (pure . f))
