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


-- import           GHC.TypeLits
-- import           Learn.Neural.Layer
-- import           Learn.Neural.Network
-- import           Type.Class.Known
import           Data.Kind
import           Data.List
import           Data.Profunctor
import           Data.Type.Combinator
import           Learn.Neural.Loss
import           Numeric.BLAS
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
    :: forall p b i o. (BLAS b, Fractional p, Num (b i), Num (b o))
    => Double
    -> LossFunction o
    -> (forall s. OpB s '[b i, p] '[b o])
    -> Optimizer (b i, b o) p
sgdOptimizer r l run = MkO () $ \(x, t) p () ->
    let o :: BPOp s '[ b i, p ]  '[ Scalar b ]
        o = withInps $ \inps -> do
              y <- run ~$ inps
              only <$> (l t ~$ (y :< Ø))
    in  case gradBPOp o (x ::< p ::< Ø) of
          _ :< I g :< Ø -> (p - realToFrac r * g, ())
        
sgdMiniBatchOptimizer
    :: forall f p b i o. (BLAS b, Fractional p, Num (b i), Num (b o), Foldable f)
    => Double
    -> LossFunction o
    -> (forall s. OpB s '[b i, p] '[b o])
    -> Optimizer (f (b i, b o)) p
sgdMiniBatchOptimizer r l run = MkO () $ \xts p () ->
    let f :: b i -> b o -> p
        f x t = case gradBPOp o (x ::< p ::< Ø) of
                  _ :< I gr :< Ø -> gr
          where
            o :: BPOp s '[ b i, p ] '[ Scalar b ]
            o = withInps $ \inps -> do
              y <- run ~$ inps
              only <$> (l t ~$ (y :< Ø))
        g = F.fold (lmap (uncurry f) F.mean) xts
    in  (p - realToFrac r * g, ())

