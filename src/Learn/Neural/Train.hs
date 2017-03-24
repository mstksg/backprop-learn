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
import           Learn.Neural.Layer
import           Learn.Neural.Loss
import           Learn.Neural.Network
import           Numeric.BLASTensor
import           Numeric.Backprop
import           Type.Class.Known
import qualified Control.Foldl        as F

data Optimizer
        :: (Type -> Type)
        -> (BShape -> Type)
        -> LChain
        -> [LChain]
        -> BShape
        -> Type where
    MkO :: { oState
                :: s
           , oUpdate
                :: f (b i, b o)
                -> Network 'FeedForward b (i :~ c) hs o
                -> s
                -> (Network 'FeedForward b (i :~ c) hs o, s)
           }
        -> Optimizer f b (i :~ c) hs o

sgdOptimizer
    :: forall b i c hs o. (Num (b i), Num (b o), BLASTensor b, Known (NetStruct 'FeedForward b (i :~ c) hs) o)
    => Double
    -> LossFunction o
    -> Optimizer I b (i :~ c) hs o
sgdOptimizer r l = MkO () $ \(I (x, t)) n () ->
    let o :: BPOp s '[ b i, Network 'FeedForward b (i :~ c) hs o ] '[ Scalar b ]
        o = withInps $ \inps -> do
              y <- networkOpPure ~$ inps
              only <$> (l t ~$ (y :< Ø))
    in  case gradBPOp o (x ::< n ::< Ø) of
          _ :< I g :< Ø -> (n - realToFrac r * g, ())

sgdMiniBatchOptimizer
    :: forall b i c hs o f.
     ( Num (b i)
     , Num (b o)
     , BLASTensor b
     , Known (NetStruct 'FeedForward b (i :~ c) hs) o
     , Foldable f
     )
    => Double
    -> LossFunction o
    -> Optimizer f b (i :~ c) hs o
sgdMiniBatchOptimizer r l = MkO () $ \xts n () ->
    let f :: b i -> b o -> Network 'FeedForward b (i :~ c) hs o
        f x t = case gradBPOp o (x ::< n ::< Ø) of
                  _ :< I gr :< Ø -> gr
          where
            o :: BPOp s '[ b i, Network 'FeedForward b (i :~ c) hs o ] '[ Scalar b ]
            o = withInps $ \inps -> do
              y <- networkOpPure ~$ inps
              only <$> (l t ~$ (y :< Ø))
        g = F.fold (lmap (uncurry f) F.mean) xts
    in  (n - realToFrac r * g, ())


runOptimizer
    :: f (b i, b o)
    -> Network 'FeedForward b (i :~ c) hs o
    -> Optimizer f b (i :~ c) hs o
    -> (Network 'FeedForward b (i :~ c) hs o, Optimizer f b (i :~ c) hs o)
runOptimizer x n = \case
    MkO s u -> case u x n s of
                 (n', s') -> (n', MkO s' u)

runOptimizer_
    :: f (b i, b o)
    -> Network 'FeedForward b (i :~ c) hs o
    -> Optimizer f b (i :~ c) hs o
    -> Network 'FeedForward b (i :~ c) hs o
runOptimizer_ x n = \case
    MkO s u -> case u x n s of
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

