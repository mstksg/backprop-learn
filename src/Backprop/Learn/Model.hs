{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Backprop.Learn.Model (
    module M
  , runLearn_, runLearnStoch_, runLearnStateless_, runLearnStochStateless_
  , gradLearn, gradLearnStoch
  ) where

import           Backprop.Learn.Model.Class       as M
import           Backprop.Learn.Model.Combinator  as M
import           Backprop.Learn.Model.Function    as M
import           Backprop.Learn.Model.Neural      as M
import           Backprop.Learn.Model.Neural.LSTM as M
import           Backprop.Learn.Model.Parameter   as M
import           Backprop.Learn.Model.Regression  as M
import           Backprop.Learn.Model.State       as M
import           Backprop.Learn.Model.Stochastic  as M
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Bifunctor
import           Data.Word
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import qualified Data.Vector.Unboxed              as VU
import qualified System.Random.MWC                as MWC

-- TODO: this can be more efficient by breaking out into separate functions
runLearn_
    :: (Learn a b l, MaybeC Num (LStateMaybe l), Num b)
    => l
    -> LParam_ I l
    -> a
    -> LState_ I l
    -> (b, LState_ I l)
runLearn_ l mp x ms = case mp of
    N_ -> case ms of
      N_       -> (evalBP (runLearnStateless l N_) x, N_)
      J_ (I s) -> second (J_ . I) . t2Tup
                . evalBP2 (\x' s' -> uncurry (isoVar2 T2 t2Tup)
                                       . second fromJ_
                                       $ runLearn l N_ x' (J_ s')
                          ) x
                $ s
    J_ (I p) -> case ms of
      N_       -> (evalBP2 (runLearnStateless l . J_) p x, N_)
      J_ (I s) -> second (J_ . I) . t2Tup
                . evalBPN (\(p' :< x' :< s' :< Ø) ->
                                uncurry (isoVar2 T2 t2Tup)
                              . second fromJ_
                              $ runLearn l (J_ p') x' (J_ s')
                          )
                $ (p ::< x ::< s ::< Ø)

runLearnStoch_
    :: (Learn a b l, MaybeC Num (LStateMaybe l), Num b, PrimMonad m)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> a
    -> LState_ I l
    -> m (b, LState_ I l)
runLearnStoch_ l g mp x ms = do
    -- TODO: is this the best way to handle this?
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ case mp of
      N_ -> case ms of
        N_       -> (, N_) $ evalBP (\x' -> runST $ do
            g' <- MWC.initialize seed
            runLearnStochStateless l g' N_ x'
          ) x
        J_ (I s) -> second (J_ . I) . t2Tup $ evalBP2 (\x' s' -> runST $ do
            g' <- MWC.initialize seed
            uncurry (isoVar2 T2 t2Tup) . second fromJ_
              <$> runLearnStoch l g' N_ x' (J_ s')
          ) x s
      J_ (I p) -> case ms of
        N_       -> (, N_) $ evalBP2 (\p' x' -> runST $ do
            g' <- MWC.initialize seed
            runLearnStochStateless l g' (J_ p') x'
          ) p x
        J_ (I s) -> second (J_ . I) . t2Tup $ evalBPN (\(p' :< x' :< s' :< Ø) -> runST $ do
            g' <- MWC.initialize seed
            uncurry (isoVar2 T2 t2Tup) . second fromJ_
              <$> runLearnStoch l g' (J_ p') x' (J_ s')
          ) (p ::< x ::< s ::< Ø)

runLearnStateless_
    :: (Learn a b l, NoState l)
    => l
    -> LParam_ I l
    -> a
    -> b
runLearnStateless_ l = \case
    N_       -> evalBP  (runLearnStateless l N_  )
    J_ (I p) -> evalBP2 (runLearnStateless l . J_) p

runLearnStochStateless_
    :: (Learn a b l, NoState l, PrimMonad m)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> a
    -> m b
runLearnStochStateless_ l g mp x = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ case mp of
      N_       -> evalBP  (\x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless l g' N_ x'
        ) x
      J_ (I p) -> evalBP2 (\p' x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless l g' (J_ p') x'
        ) p x

gradLearn
    :: (Learn a b l, NoState l, Num a, Num b, MaybeC Num (LParamMaybe l))
    => l
    -> LParam_ I l
    -> a
    -> (LParam_ I l, a)
gradLearn l = \case
    N_       ->       (N_,)    . gradBP  (runLearnStateless l   N_)
    J_ (I p) -> first (J_ . I) . gradBP2 (runLearnStateless l . J_) p

gradLearnStoch
    :: (Learn a b l, NoState l, Num a, Num b, MaybeC Num (LParamMaybe l), PrimMonad m)
    => l
    -> MWC.Gen (PrimState m)
    -> LParam_ I l
    -> a
    -> m (LParam_ I l, a)
gradLearnStoch l g mp x = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ case mp of
      N_       ->       (N_,)    $ gradBP  (\x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless l g' N_ x'
        ) x
      J_ (I p) -> first (J_ . I) $ gradBP2 (\p' x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless l g' (J_ p') x'
        ) p x
