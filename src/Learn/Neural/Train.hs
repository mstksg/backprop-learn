{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
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
  , sgdOptimizer
  , sgdMiniBatchOptimizer
  , slidingParts
  , slidingPartsSplit
  , slidingPartsLast
  ) where


import           Data.Foldable
import           Data.Kind
import           Data.List hiding        ((\\))
import           Data.Maybe
import           Data.Profunctor
import           Data.Type.Combinator
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Util
import           Data.Type.Vector hiding (transpose)
import           Learn.Neural.Loss
import           Numeric.Backprop
import           Type.Class.Known
import           Type.Family.Nat
import qualified Control.Foldl           as F
import qualified Data.Type.Nat           as TCN

data Optimizer :: Type -> Type -> Type where
    MkO :: { oState  :: s
           , oUpdate :: a -> p -> s -> (p, s)
           }
        -> Optimizer a p

runOptimizer
    :: a
    -> p
    -> Optimizer a p
    -> (p, Optimizer a p)
runOptimizer x p = \case
    MkO s u -> case u x p s of
                 (p', s') -> (p', MkO s' u)

runOptimizer_
    :: a
    -> p
    -> Optimizer a p
    -> p
runOptimizer_ x p = \case
    MkO s u -> case u x p s of
                 (p', _) -> p'

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

sgdOptimizer
    :: forall p as bs c. (Fractional p, Num c, Every Num as, Every Num bs, Known Length as)
    => Double
    -> (forall s. OpB s (p ': as) bs)
    -> LossFunction bs c
    -> Optimizer (Tuple as, Tuple bs) p
sgdOptimizer r run l = MkO () $ \(xs, ts) p () ->
    let o :: BPOp s (p ': as) '[ c ]
        o = withInps $ \inps -> do
              ys <- run ~$$ inps
              only <$> (l ts ~$ ys)
    in  case gradBPOp o (p ::< xs) of
          I g :< _ -> (p - realToFrac r * g, ())

sgdMiniBatchOptimizer
    :: forall f p as bs c. (Foldable f, Fractional p, Num c, Every Num as, Every Num bs, Known Length as)
    => Double
    -> (forall s. OpB s (p ': as) bs)
    -> LossFunction bs c
    -> Optimizer (f (Tuple as, Tuple bs)) p
sgdMiniBatchOptimizer r run l = MkO () $ \xts p () ->
    let f :: Tuple as -> Tuple bs -> p
        f xs ts = case gradBPOp o (p ::< xs) of
                    I gr :< _ -> gr
          where
            o :: BPOp s (p ': as) '[ c ]
            o = withInps $ \inps -> do
              ys <- run ~$$ inps
              only <$> (l ts ~$ ys)
        g = F.fold (lmap (uncurry f) F.mean) xts
    in  (p - realToFrac r * g, ())

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
