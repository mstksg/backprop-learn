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
    DeParam(..)
  , dpDeterm
  , DeParamAt(..)
  , dpaDeterm
  , ReParam
  , rpDeterm
  ) where

import           Backprop.Learn.Model.Class
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Typeable
import           Numeric.Backprop
import qualified System.Random.MWC          as MWC

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
  deriving (Typeable)

-- | Create a 'DeParam' from a deterministic, non-stochastic parameter.
dpDeterm :: p -> l -> DeParam p l
dpDeterm p = DP p (const (pure p))

instance (Learn a b l, LParamMaybe l ~ 'Just p) => Learn a b (DeParam p l) where
    type LParamMaybe (DeParam p l) = 'Nothing
    type LStateMaybe (DeParam p l) = LStateMaybe l

    runLearn DP{..} _ = runLearn _dpLearn (J_ (constVar _dpParam))
    runLearnStoch DP{..} g _ x s = do
      p <- constVar <$> _dpParamStoch g
      runLearnStoch _dpLearn g (J_ p) x s

-- | Wrapping a mode with @'DeParamAt' pq p q@ says that the mode's
-- parameter @pq@ can be split into @p@ and @q@, and fixes @q@ to a given
-- fixed (or stochastic with a fixed distribution) value.  The model now
-- effectively has parameter @p@ only, and the @q@ part will not be
-- backpropagated.
--
-- 'DeParam' is essentially 'DeParamAt' where @p@ is '()' or 'T0'.
data DeParamAt :: Type -> Type -> Type -> Type -> Type where
    DPA :: { _dpaSplit      :: pq -> (p, q)
           , _dpaJoin       :: p -> q -> pq
           , _dpaParam      :: q
           , _dpaParamStoch :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m q
           , _dpaLearn      :: l
           }
        -> DeParamAt pq p q l
  deriving (Typeable)

-- | Create a 'DeParamAt' from a deterministic, non-stochastic fixed value
-- as a part of the parameter.
dpaDeterm :: (pq -> (p, q)) -> (p -> q -> pq) -> q -> l -> DeParamAt pq p q l
dpaDeterm s j q = DPA s j q (const (pure q))

instance (Learn a b l, LParamMaybe l ~ 'Just pq, Backprop pq, Backprop p, Backprop q)
        => Learn a b (DeParamAt pq p q l) where
    type LParamMaybe (DeParamAt pq p q l) = 'Just p
    type LStateMaybe (DeParamAt pq p q l) = LStateMaybe l

    runLearn DPA{..} (J_ p) = runLearn _dpaLearn (J_ p')
      where
        p' = isoVar2 _dpaJoin _dpaSplit p (constVar _dpaParam)

    runLearnStoch DPA{..} g (J_ p) x s = do
        q <- _dpaParamStoch g
        let p' = isoVar2 _dpaJoin _dpaSplit p (constVar q)
        runLearnStoch _dpaLearn g (J_ p') x s


-- | Pre-apply a function to the parameter before the original model sees
-- it.  A @'ReParam' p q@ turns a model taking @p@ into a model taking @q@.
--
-- Note that a @'ReParam' p ''Nothing'@ is essentially the same as
-- a @'DeParam' p@, and one could implement @'DeParamAt' pq p q@ in terms of
-- @'ReParam' pq (''Just' p)@.
data ReParam :: Type -> Maybe Type -> Type -> Type where
    RP :: { _rpFrom      :: forall s. Reifies s W => Mayb (BVar s) q -> BVar s p
          , _rpFromStoch :: forall m s. (PrimMonad m, Reifies s W) => MWC.Gen (PrimState m) -> Mayb (BVar s) q -> m (BVar s p)
          , _rpLearn     :: l
          }
       -> ReParam p q l
  deriving (Typeable)

instance (Learn a b l, LParamMaybe l ~ 'Just p) => Learn a b (ReParam p q l) where
    type LParamMaybe (ReParam p q l) = q
    type LStateMaybe (ReParam p q l) = LStateMaybe l

    runLearn RP{..} q = runLearn _rpLearn (J_ (_rpFrom q))
    runLearnStoch RP{..} g q x s = do
      p <- _rpFromStoch g q
      runLearnStoch _rpLearn g (J_ p) x s

-- | Create a 'ReParam' from a deterministic, non-stochastic
-- transformation function.
rpDeterm
    :: (forall s. Reifies s W => Mayb (BVar s) q -> BVar s p)
    -> l
    -> ReParam p q l
rpDeterm f = RP f (const (pure . f))
