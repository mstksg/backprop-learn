{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeInType       #-}
{-# LANGUAGE TypeOperators    #-}

module Learn.Neural.Train (
    Optimizer(..)
  , runOptimizer
  , runOptimizer_
  , optimizeList
  , optimizeList_
  ) where


import           Data.Kind
import           Data.List
import           Data.Type.Combinator
import           Learn.Neural.Layer
import           Learn.Neural.Loss
import           Learn.Neural.Network
import           Numeric.BLASTensor
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           Type.Class.Known

data Optimizer
        :: (Type -> Type)
        -> (BShape -> Type)
        -> LChain
        -> [LChain]
        -> BShape
        -> Type where
    MkO :: { oState
                :: s
           , oLoss
                :: LossFunction o
           , oUpdate
                :: f (b i, b o)
                -> Network 'FeedForward b (i :~ c) hs o
                -> s
                -> (Network 'FeedForward b (i :~ c) hs o, s)
           }
        -> Optimizer f b (i :~ c) hs o

stochasticGradientDescent
    :: (Num (b i), Num (b o), BLASTensor b, Known (NetStruct 'FeedForward b (i :~ c) hs) o)
    => Double
    -> LossFunction o
    -> Optimizer I b (i :~ c) hs o
stochasticGradientDescent r l = MkO () l $ \(I (x, t)) n () ->
    case gradOpB networkOp (x ::< n ::< Ø) of
      _ :< I g :< Ø -> (n + realToFrac r * g, ())

runOptimizer
    :: f (b i, b o)
    -> Network 'FeedForward b (i :~ c) hs o
    -> Optimizer f b (i :~ c) hs o
    -> (Network 'FeedForward b (i :~ c) hs o, Optimizer f b (i :~ c) hs o)
runOptimizer x n = \case
    MkO s l u -> case u x n s of
                   (n', s') -> (n', MkO s' l u)

runOptimizer_
    :: f (b i, b o)
    -> Network 'FeedForward b (i :~ c) hs o
    -> Optimizer f b (i :~ c) hs o
    -> Network 'FeedForward b (i :~ c) hs o
runOptimizer_ x n = \case
    MkO s l u -> case u x n s of
                   (n', _) -> n'

data STup a b = STup !a !b

optimizeList
    :: [f (b i, b o)]
    -> Network 'FeedForward b (i :~ c) hs o
    -> Optimizer f b (i :~ c) hs o
    -> (Network 'FeedForward b (i :~ c) hs o, Optimizer f b (i :~ c) hs o)
optimizeList xs n0 o0 = case foldl' f (STup n0 o0) xs of
    STup n o -> (n, o)
  where
    f (STup n o) x = case runOptimizer x n o of
      (n', o') -> STup n' o'

optimizeList_
    :: [f (b i, b o)]
    -> Network 'FeedForward b (i :~ c) hs o
    -> Optimizer f b (i :~ c) hs o
    -> Network 'FeedForward b (i :~ c) hs o
optimizeList_ xs n0 = fst . optimizeList xs n0

