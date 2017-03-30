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
import           Learn.Neural.Loss
import           Numeric.Backprop
import qualified Control.Foldl           as F

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
    :: forall p a b c. (Fractional p, Num a, Num b, Num c)
    => Double
    -> (forall s. OpB s '[p, a] '[ b ])
    -> LossFunction '[ b ] c
    -> Optimizer (a, b) p
sgdOptimizer r run l = MkO () $ \(x, t) p () ->
    let o :: BPOp s '[ p, a ] '[ c ]
        o = withInps $ \inps -> do
              y <- run ~$ inps
              only <$> (l (only_ t) ~$ (y :< Ø))
    in  case gradBPOp o (p ::< x ::< Ø) of
          I g :< _ :< Ø -> (p - realToFrac r * g, ())

sgdMiniBatchOptimizer
    :: forall f p a b c. (Foldable f, Fractional p, Num a, Num b, Num c)
    => Double
    -> (forall s. OpB s '[ p, a ] '[ b ])
    -> LossFunction '[ b ] c
    -> Optimizer (f (a, b)) p
sgdMiniBatchOptimizer r run l = MkO () $ \xts p () ->
    let f :: a -> b -> p
        f x t = case gradBPOp o (p ::< x ::< Ø) of
                  I gr :< _ :< Ø -> gr
          where
            o :: BPOp s '[ p, a ] '[ c ]
            o = withInps $ \inps -> do
              y <- run ~$ inps
              only <$> (l (only_ t) ~$ (y :< Ø))
        g = F.fold (lmap (uncurry f) F.mean) xts
    in  (p - realToFrac r * g, ())

