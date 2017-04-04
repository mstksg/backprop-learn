{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Learn.Neural.Train (
    Optimizer(..)
  , runOptimizer
  , runOptimizer_
  , optimizeList
  , optimizeList_
  , optimizeListBatches
  , optimizeListBatches_
  , batching
  , sgdOptimizer
  , adamOptimizer
  , Adam(..)
  , slidingParts
  , slidingPartsSplit
  , slidingPartsLast
  , asFeedback
  , Default(..)
  ) where


import           Data.Default
import           Data.Foldable
import           Data.Kind
import           Data.List hiding        ((\\))
import           Data.List.Split
import           Data.Maybe
import           Data.Profunctor
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

data Optimizer :: Type -> Type -> Type where
    MkO :: { oState  :: s
           , oGrad   :: a -> p -> p
           , oUpdate :: p -> p -> s -> (p, s)       -- ^ params, grad, state
           }
        -> Optimizer a p

runOptimizer
    :: a
    -> p
    -> Optimizer a p
    -> (p, Optimizer a p)
runOptimizer x p = \case
    MkO s g u ->
      let gr = g x p
          (p', s') = u p gr s
      in  (p', MkO s' g u)

runOptimizer_
    :: a
    -> p
    -> Optimizer a p
    -> p
runOptimizer_ x p = fst . runOptimizer x p

data STup a b = STup !a !b

optimizeList
    :: [a]
    -> p
    -> Optimizer a p
    -> (p, Optimizer a p)
optimizeList xs p0 o0 = case foldl' f (STup p0 o0) xs of
    STup p o -> (p, o)
  where
    f (STup p o) x = case runOptimizer x p o of
      (p', o') -> STup p' o'

optimizeList_
    :: [a]
    -> p
    -> Optimizer a p
    -> p
optimizeList_ xs p0 = fst . optimizeList xs p0

optimizeListBatches
    :: [a]
    -> p
    -> Optimizer [a] p
    -> Int
    -> (p, Optimizer [a] p)
optimizeListBatches xs p0 o b = optimizeList (chunksOf b xs) p0 o

optimizeListBatches_
    :: [a]
    -> p
    -> Optimizer [a] p
    -> Int
    -> p
optimizeListBatches_ xs p0 o b = optimizeList_ (chunksOf b xs) p0 o

sgdOptimizer
    :: forall p as bs c. (Fractional p, Num c, Every Num as, Every Num bs, Known Length as)
    => Double
    -> (forall s. OpB s (p ': as) bs)
    -> LossFunction bs c
    -> Optimizer (Tuple as, Tuple bs) p
sgdOptimizer r run l = MkO () g u
  where
    g :: (Tuple as, Tuple bs) -> p -> p
    g (xs, ts) p = getI . head' $ gradBPOp o (p ::< xs)
      where
        o :: BPOp s (p ': as) '[ c ]
        o = withInps $ \inps -> do
          ys <- run ~$$ inps
          only <$> (l ts ~$ ys)
    u :: p -> p -> () -> (p, ())
    u p gr () = (p - realToFrac r * gr, ())

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
adamOptimizer Adam{..} run l = MkO s0 g u
  where
    s0 :: (Double, p, p)
    s0 = (1, 0, 0)
    g :: (Tuple as, Tuple bs) -> p -> p
    g (xs, ts) p = getI . head' $ gradBPOp o (p ::< xs)
      where
        o :: BPOp s (p ': as) '[ c ]
        o = withInps $ \inps -> do
              ys <- run ~$$ inps
              only <$> (l ts ~$ ys)
    u :: p -> p -> (Double, p, p) -> (p, (Double, p, p))
    u p0 gr (t, m0, v0) = (p1, (t + 1, m1, v1))
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
    :: forall f a p. (Foldable f, Fractional p)
    => Optimizer a p
    -> Optimizer (f a) p
batching = \case
    MkO s g u ->
      let g' :: f a -> p -> p
          g' xs p = F.fold (lmap (`g` p) F.mean) xs
      in  MkO s g' u

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
