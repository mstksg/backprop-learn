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
  ) where


import           Data.Kind
import           Data.List
import           Data.Profunctor
import           Data.Type.Combinator
import           Data.Type.Index
import           Data.Type.Length
import           Learn.Neural.Loss
import           Numeric.Backprop
import           Type.Class.Known
import qualified Control.Foldl        as F

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

