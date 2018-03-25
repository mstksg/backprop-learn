{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

module Learn.Neural.Train (
    OptimizerM(..)
  , Optimizer
  , pattern MkO
  , runOptimizer
  , runOptimizerM
  , runOptimizer_
  , runOptimizerM_
  , optimizeList
  , optimizeListM
  , optimizeList_
  , optimizeListM_
  , optimizeListBatches
  , optimizeListBatchesM
  , optimizeListBatches_
  , optimizeListBatchesM_
  , batching
  , sgdOptimizer
  , sgdOptimizerM
  , adamOptimizer
  , adamOptimizerM
  , Adam(..)
  , slidingParts
  , slidingPartsSplit
  , slidingPartsLast
  , asFeedback
  , Default(..)
  ) where


-- import           Data.Bifunctor
-- import           Data.Foldable
import           Data.Default
import           Data.Kind
import           Data.List hiding        ((\\))
import           Data.List.Split
import           Data.Maybe
import           Data.Type.Combinator
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Util
import           Data.Type.Vector hiding (transpose, head', m0, m1)
import           Learn.Neural.Loss
import           Numeric.Backprop
import           Type.Class.Known
import           Type.Family.Nat
import qualified Control.Foldl           as F
import qualified Data.Type.Nat           as TCN

data OptimizerM :: (Type -> Type) -> Type -> Type -> Type where
    MkOM :: { oState  :: s
            , oGrad   :: a -> p -> m p
            , oUpdate :: p -> p -> s -> m (p, s)       -- ^ params, grad, state
            }
         -> OptimizerM m a p

type Optimizer = OptimizerM I

pattern MkO :: s -> (a -> p -> p) -> (p -> p -> s -> (p, s)) -> Optimizer a p
pattern MkO s g u <- MkOM s (\g' x -> getI . g' x -> g) (\u' x y -> getI . u' x y -> u)
  where
    MkO s g u = MkOM s (\x -> I . g x) (\x y -> I . u x y)

runOptimizer
    :: a
    -> p
    -> Optimizer a p
    -> (p, Optimizer a p)
runOptimizer x p = getI . runOptimizerM x p

runOptimizerM
    :: Monad m
    => a
    -> p
    -> OptimizerM m a p
    -> m (p, OptimizerM m a p)
runOptimizerM x p = \case
    MkOM s g u -> do
      gr       <- g x p
      (p', s') <- u p gr s
      return (p', MkOM s' g u)

runOptimizer_
    :: a
    -> p
    -> Optimizer a p
    -> p
runOptimizer_ x p = fst . runOptimizer x p

runOptimizerM_
    :: Monad m
    => a
    -> p
    -> OptimizerM m a p
    -> m p
runOptimizerM_ x p = fmap fst . runOptimizerM x p

optimizeList
    :: forall a p. ()
    => [a]
    -> p
    -> Optimizer a p
    -> (p, Optimizer a p)
optimizeList xs p0 o0 = F.fold f xs
  where
    f :: F.Fold a (p, Optimizer a p)
    f = F.Fold (\(!p, !o) x -> runOptimizer x p o)
               (p0, o0)
               id

optimizeListM
    :: forall m a p. Monad m
    => [a]
    -> p
    -> OptimizerM m a p
    -> m (p, OptimizerM m a p)
optimizeListM xs p0 o0 = F.foldM f xs
  where
    f :: F.FoldM m a (p, OptimizerM m a p)
    f = F.FoldM (\(!p, !o) x -> runOptimizerM x p o)
                (return (p0, o0))
                return

optimizeList_
    :: [a]
    -> p
    -> Optimizer a p
    -> p
optimizeList_ xs p0 = fst . optimizeList xs p0

optimizeListM_
    :: Monad m
    => [a]
    -> p
    -> OptimizerM m a p
    -> m p
optimizeListM_ xs p0 = fmap fst . optimizeListM xs p0

optimizeListBatches
    :: [a]
    -> p
    -> Optimizer [a] p
    -> Int
    -> (p, Optimizer [a] p)
optimizeListBatches xs p0 o b = optimizeList (chunksOf b xs) p0 o

optimizeListBatchesM
    :: Monad m
    => [a]
    -> p
    -> OptimizerM m [a] p
    -> Int
    -> m (p, OptimizerM m [a] p)
optimizeListBatchesM xs p0 o b = optimizeListM (chunksOf b xs) p0 o

optimizeListBatches_
    :: [a]
    -> p
    -> Optimizer [a] p
    -> Int
    -> p
optimizeListBatches_ xs p0 o b = optimizeList_ (chunksOf b xs) p0 o

optimizeListBatchesM_
    :: Monad m
    => [a]
    -> p
    -> OptimizerM m [a] p
    -> Int
    -> m p
optimizeListBatchesM_ xs p0 o b = optimizeListM_ (chunksOf b xs) p0 o

sgdOptimizer
    :: forall p as bs c. (Fractional p, Num c, Every Num as, Every Num bs, Known Length as)
    => Double
    -> (forall s. OpB s (p ': as) bs)
    -> LossFunction bs c
    -> Optimizer (Tuple as, Tuple bs) p
sgdOptimizer r run = sgdOptimizerM r (return (OpBS run))

sgdOptimizerM
    :: forall m p as bs c. (Fractional p, Num c, Every Num as, Every Num bs, Known Length as, Monad m)
    => Double
    -> m (OpBS (p ': as) bs)
    -> LossFunction bs c
    -> OptimizerM m (Tuple as, Tuple bs) p
sgdOptimizerM r run l = MkOM () g u
  where
    g :: (Tuple as, Tuple bs) -> p -> m p
    g (xs, ts) p = flip fmap run $ \(o0 :: OpBS (p ': as) bs) ->
        let o :: BPOp s (p ': as) '[ c ]
            o = withInps $ \inps -> do
              ys <- runOpBS o0 ~$$ inps
              only <$> (l ts ~$ ys)
        in  getI . head' $ gradBPOp o (p ::< xs)
    u :: p -> p -> () -> m (p, ())
    u p gr () = return (p - realToFrac r * gr, ())

data Adam = Adam
    { adamStep    :: Double
    , adamDecay1  :: Double
    , adamDecay2  :: Double
    , adamEpsilon :: Double
    }
  deriving (Show, Eq)

instance Default Adam where
    def = Adam { adamStep    = 0.001
               , adamDecay1  = 0.9
               , adamDecay2  = 0.999
               , adamEpsilon = 1e-8
               }

adamOptimizer
    :: forall p as bs c. (Floating p, Num c, Every Num as, Every Num bs, Known Length as)
    => Adam
    -> (forall s. OpB s (p ': as) bs)
    -> LossFunction bs c
    -> Optimizer (Tuple as, Tuple bs) p
adamOptimizer a run = adamOptimizerM a (return (OpBS run))

adamOptimizerM
    :: forall m p as bs c. (Floating p, Num c, Every Num as, Every Num bs, Known Length as, Monad m)
    => Adam
    -> m (OpBS (p ': as) bs)
    -> LossFunction bs c
    -> OptimizerM m (Tuple as, Tuple bs) p
adamOptimizerM Adam{..} run l = MkOM s0 g u
  where
    s0 :: (Double, p, p)
    s0 = (1, 0, 0)
    g :: (Tuple as, Tuple bs) -> p -> m p
    g (xs, ts) p = flip fmap run $ \(o0 :: OpBS (p ': as) bs) ->
        let o :: BPOp s (p ': as) '[ c ]
            o = withInps $ \inps -> do
              ys <- runOpBS o0 ~$$ inps
              only <$> (l ts ~$ ys)
        in  getI . head' $ gradBPOp o (p ::< xs)
    u :: p -> p -> (Double, p, p) -> m (p, (Double, p, p))
    u p0 gr (t, m0, v0) = return (p1, (t + 1, m1, v1))
      where
        m1, v1 :: p
        m1 = ad1 * m0 + ad1' * gr
        v1 = ad2 * v0 + ad2' * gr * gr
        mHat = m1 / (1 - realToFrac (adamDecay1 ** t))
        vHat = v1 / (1 - realToFrac (adamDecay2 ** t))
        p1 = p0 - as * mHat / (sqrt vHat + ae)
    ad1, ad1', ad2, ad2', as, ae :: p
    ad1  = realToFrac adamDecay1
    ad1' = realToFrac (1 - adamDecay1)
    ad2  = realToFrac adamDecay2
    ad2' = realToFrac (1 - adamDecay2)
    as   = realToFrac adamStep
    ae   = realToFrac adamEpsilon

batching
    :: forall f m a p. (Foldable f, Fractional p, Monad m)
    => OptimizerM m a p
    -> OptimizerM m (f a) p
batching = \case
    MkOM s g u ->
      let g' :: f a -> p -> m p
          g' xs p = F.foldM (premapM' (`g` p) (F.generalize F.mean)) xs
      in  MkOM s g' u

premapM'
    :: Monad m
    => (a -> m b)
    -> F.FoldM m b r
    -> F.FoldM m a r
premapM' f (F.FoldM step begin done) = F.FoldM step' begin done
  where
    step' x a = step x =<< f a
{-# INLINABLE premapM' #-}

slidingParts
    :: TCN.Nat n
    -> [a]
    -> [Vec n a]
slidingParts n xs = mapMaybe (takeVec n) $ slides
  where
    slides = transpose . take (TCN.natVal n) . flip unfoldr xs $ \ys ->
      case ys of
        []   -> Nothing
        _:zs -> Just (ys, zs)

slidingPartsSplit
    :: TCN.Nat n
    -> [(a, b)]
    -> [(Vec n a, Vec n b)]
slidingPartsSplit n = map unzipVec . slidingParts n

slidingPartsLast
    :: TCN.Nat ('S n)
    -> [(a, b)]
    -> [(Vec ('S n) a, b)]
slidingPartsLast n = map (\xy -> (fst <$> xy, snd . getI $ last' xy))
                   . slidingParts n

asFeedback :: [a] -> [(a, a)]
asFeedback xs = zip xs (drop 1 xs)
