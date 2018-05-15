{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module Backprop.Learn.Model (
    module M, Backprop(..)
  -- * Running and Grad
  , runModel, runModelStoch, runModelStateless, runModelStochStateless
  , gradModel, gradModelStoch
  -- * Work with parameters
  , initParam, initParamNormal
  , encodeParam, decodeParam, decodeParamOrFail, saveParam, loadParam, loadParamOrFail
  -- * Iterated runners
  , iterateModel, iterateModelM, iterateModelStoch
  , scanModel, scanModelStoch
  -- * No final state
  , iterateModel_, iterateModelM_, iterateModelStoch_
  , scanModel_, scanModelStoch_
  -- * "Prime" runners
  , primeModel, primeModelStoch, selfPrime, selfPrimeM
  ) where

import           Backprop.Learn.Initialize
import           Backprop.Learn.Model.Combinator  as M
import           Backprop.Learn.Model.Function    as M
import           Backprop.Learn.Model.Neural      as M
import           Backprop.Learn.Model.Neural.LSTM as M
import           Backprop.Learn.Model.Parameter   as M
import           Backprop.Learn.Model.Regression  as M
import           Backprop.Learn.Model.State       as M
import           Backprop.Learn.Model.Stochastic  as M
import           Backprop.Learn.Model.Types       as M
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Foldable
import           Data.Functor.Identity
import           Data.Word
import           Numeric.Backprop
import           Statistics.Distribution
import           Type.Class.Higher
import qualified Data.Binary                      as Bi
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.Vector.Unboxed              as VU
import qualified System.Random.MWC                as MWC

-- TODO: this can be more efficient by breaking out into separate functions
runModel
    :: forall p s a b. (MaybeC Backprop s, Backprop b)
    => Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> (b, Mayb I s)
runModel f mp x ms = evalBP0 go
  where
    go :: forall z. Reifies z W => BVar z (b, Mayb I s)
    go = case ms' of
        N_    -> T2 y $ auto N_
        J_ s' -> T2 y $ isoVar (J_ . I) (getI . fromJ_) s'
      where
        y :: BVar z b
        ms' :: Mayb (BVar z) s
        (y, ms') = runLearn f (map1 (auto . getI) mp)
                              (auto x)
                              (map1 (auto . getI) ms)

-- TODO: this can be more efficient by breaking out into separate functions
runModelStoch
    :: forall p s a b m. (MaybeC Backprop s, Backprop b, PrimMonad m)
    => Model p s a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> a
    -> Mayb I s
    -> m (b, Mayb I s)
runModelStoch f g mp x ms = do
    -- TODO: is this the best way to handle this?
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ evalBP0 (runST (go seed))
  where
    go  :: forall q z. Reifies z W
        => VU.Vector Word32
        -> ST q (BVar z (b, Mayb I s))
    go seed = do
      g' <- MWC.initialize seed
      (y :: BVar z b, ms') <- runLearnStoch f g'
        (map1 (auto . getI) mp)
        (auto x)
        (map1 (auto . getI) ms)
      pure $ case ms' of
        N_    -> T2 y $ auto N_
        J_ s' -> T2 y $ isoVar (J_ . I) (getI . fromJ_) s'

runModelStateless
    :: Model p 'Nothing a b
    -> Mayb I p
    -> a
    -> b
runModelStateless f = \case
    N_       -> evalBP  (runLearnStateless f N_  )
    J_ (I p) -> evalBP2 (runLearnStateless f . J_) p

runModelStochStateless
    :: PrimMonad m
    => Model p 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> a
    -> m b
runModelStochStateless f g mp x = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ case mp of
      N_       -> evalBP  (\x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless f g' N_ x'
        ) x
      J_ (I p) -> evalBP2 (\p' x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless f g' (J_ p') x'
        ) p x

gradModel
    :: (Backprop a, Backprop b, MaybeC Backprop p)
    => Model p 'Nothing a b
    -> Mayb I p
    -> a
    -> (Mayb I p, a)
gradModel f = \case
    N_       ->       (N_,)    . gradBP  (runLearnStateless f   N_)
    J_ (I p) -> first (J_ . I) . gradBP2 (runLearnStateless f . J_) p

gradModelStoch
    :: (Backprop a, Backprop b, MaybeC Backprop p, PrimMonad m)
    => Model p 'Nothing a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> a
    -> m (Mayb I p, a)
gradModelStoch f g mp x = do
    seed <- MWC.uniformVector @_ @Word32 @VU.Vector g 2
    pure $ case mp of
      N_       ->       (N_,)    $ gradBP  (\x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless f g' N_ x'
        ) x
      J_ (I p) -> first (J_ . I) $ gradBP2 (\p' x' -> runST $ do
          g' <- MWC.initialize seed
          runLearnStochStateless f g' (J_ p') x'
        ) p x

iterateModel
    :: (Backprop b, MaybeC Backprop s)
    => (b -> a)         -- ^ loop
    -> Int              -- ^ num times
    -> Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> ([b], Mayb I s)
iterateModel l n f p x = runIdentity . iterateModelM (Identity . l) n f p x

iterateModel_
    :: (Backprop b, MaybeC Backprop s)
    => (b -> a)         -- ^ loop
    -> Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> [b]
iterateModel_ l f p = go
  where
    go !x !s = y : go (l y) s'
      where
        (y, s') = runModel f p x s

selfPrime
    :: (Backprop b, MaybeC Backprop s)
    => (b -> a)         -- ^ loop
    -> Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> [Mayb I s]
selfPrime l f p = go
  where
    go !x !s = s' : go (l y) s'
      where
        (y, s') = runModel f p x s

iterateModelM
    :: (Backprop b, MaybeC Backprop s, Monad m)
    => (b -> m a)           -- ^ loop
    -> Int                  -- ^ num times
    -> Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> m ([b], Mayb I s)
iterateModelM l n f p = go 0
  where
    go !i !x !s
      | i <= n    = do
          let (y, s') = runModel f p x s
          (ys, s'') <- flip (go (i + 1)) s' =<< l y
          pure (y : ys, s'')
      | otherwise = pure ([], s)

iterateModelM_
    :: (Backprop b, MaybeC Backprop s, Monad m)
    => (b -> m a)           -- ^ loop
    -> Int                  -- ^ num times
    -> Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> m [b]
iterateModelM_ l n f p x = fmap fst . iterateModelM l n f p x

selfPrimeM
    :: (Backprop b, MaybeC Backprop s, Monad m)
    => (b -> m a)           -- ^ loop
    -> Int                  -- ^ num times
    -> Model p s a b
    -> Mayb I p
    -> a
    -> Mayb I s
    -> m (Mayb I s)
selfPrimeM l n f p x = fmap snd . iterateModelM l n f p x

iterateModelStoch
    :: (Backprop b, MaybeC Backprop s, PrimMonad m)
    => (b -> m a)           -- ^ loop
    -> Int                  -- ^ num times
    -> Model p s a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> a
    -> Mayb I s
    -> m ([b], Mayb I s)
iterateModelStoch l n f g p = go 0
  where
    go !i !x !s
      | i <= n    = do
          (y , s' ) <- runModelStoch f g p x s
          (ys, s'') <- flip (go (i + 1)) s' =<< l y
          pure (y : ys, s'')
      | otherwise = pure ([], s)

iterateModelStoch_
    :: (Backprop b, MaybeC Backprop s, PrimMonad m)
    => (b -> m a)           -- ^ loop
    -> Int                  -- ^ num times
    -> Model p s a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> a
    -> Mayb I s
    -> m [b]
iterateModelStoch_ l n f g p x = fmap fst . iterateModelStoch l n f g p x

scanModel
    :: (Traversable t, Backprop b, MaybeC Backprop s)
    => Model p s a b
    -> Mayb I p
    -> t a
    -> Mayb I s
    -> (t b, Mayb I s)
scanModel f p = runState . traverse (state . runModel f p)

scanModel_
    :: (Traversable t, Backprop b, MaybeC Backprop s)
    => Model p s a b
    -> Mayb I p
    -> t a
    -> Mayb I s
    -> t b
scanModel_ f p xs = fst . scanModel f p xs

primeModel
    :: (Foldable t, Backprop b, MaybeC Backprop s)
    => Model p s a b
    -> Mayb I p
    -> t a
    -> Mayb I s
    -> Mayb I s
primeModel f p = execState . traverse_ (state . runModel f p)

scanModelStoch
    :: (Traversable t, Backprop b, MaybeC Backprop s, PrimMonad m)
    => Model p s a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> t a
    -> Mayb I s
    -> m (t b, Mayb I s)
scanModelStoch f g p = runStateT . traverse (StateT . runModelStoch f g p)

scanModelStoch_
    :: (Traversable t, Backprop b, MaybeC Backprop s, PrimMonad m)
    => Model p s a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> t a
    -> Mayb I s
    -> m (t b)
scanModelStoch_ f g p xs = fmap fst . scanModelStoch f g p xs

primeModelStoch
    :: (Foldable t, Backprop b, MaybeC Backprop s, PrimMonad m)
    => Model p s a b
    -> MWC.Gen (PrimState m)
    -> Mayb I p
    -> t a
    -> Mayb I s
    -> m (Mayb I s)
primeModelStoch f g p = execStateT . traverse_ (StateT . runModelStoch f g p)

initParam
    :: (Initialize p, ContGen d, PrimMonad m)
    => model ('Just p) s a b                    -- ^ ignored
    -> d
    -> MWC.Gen (PrimState m)
    -> m p
initParam _ = initialize

initParamNormal
    :: (Initialize p, PrimMonad m)
    => model ('Just p) s a b                    -- ^ ignored
    -> Double
    -> MWC.Gen (PrimState m)
    -> m p
initParamNormal _ = initializeNormal

encodeParam
    :: Bi.Binary p
    => model ('Just p) s a b                    -- ^ ignored
    -> p
    -> BSL.ByteString
encodeParam _ = Bi.encode

decodeParam
    :: Bi.Binary p
    => model ('Just p) s a b                    -- ^ ignored
    -> BSL.ByteString
    -> p
decodeParam _ = Bi.decode

decodeParamOrFail
    :: Bi.Binary p
    => model ('Just p) s a b                    -- ^ ignored
    -> BSL.ByteString
    -> Either String p
decodeParamOrFail _ = bimap thrd thrd . Bi.decodeOrFail

saveParam
    :: Bi.Binary p
    => model ('Just p) s a b                    -- ^ ignored
    -> FilePath
    -> p
    -> IO ()
saveParam p fp = BSL.writeFile fp . encodeParam p

loadParam
    :: Bi.Binary p
    => model ('Just p) s a b                    -- ^ ignored
    -> FilePath
    -> IO p
loadParam p fp = decodeParam p <$> BSL.readFile fp

loadParamOrFail
    :: Bi.Binary p
    => model ('Just p) s a b                    -- ^ ignored
    -> FilePath
    -> IO (Either String p)
loadParamOrFail p fp = decodeParamOrFail p <$> BSL.readFile fp


thrd :: (a,b,c) -> c
thrd (_,_,z) = z
