{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Numeric.Tensor (
    Tensor(..)
  , fromScalar
  , toScalar
  , tmapOp
  , tzipNOp
  , tkonstOp
  , tsumOp
  , scaleOp
  , oneHot
  , Finite
  ) where

import           Data.Finite
import           Data.Kind
import           Data.Reflection
import           Data.Singletons.Prelude hiding (Reverse)
import           Data.Singletons.TypeLits
import           Data.Type.Util
import           Data.Type.Vector hiding        (head')
import           Numeric.AD hiding              (Scalar)
import           Numeric.AD.Internal.Reverse
import           Numeric.AD.Mode.Forward        (Forward)
import           Numeric.Backprop.Op
import           Type.Class.Higher
import           Type.Class.Known
import qualified Data.Type.Nat                  as TCN

class RealFloat (Scalar t)
        => Tensor (t :: [Nat] -> Type) where
    -- type IndexT t :: k -> Type
    type Scalar t :: Type

    genA
        :: forall f s. Applicative f
        => Sing s
        -> (Prod Finite s -> f (Scalar t))
        -> f (t s)

    gen :: forall s. Sing s
        -> (Prod Finite s -> Scalar t)
        -> t s
    gen s f = getI $ genA s (I . f)

    tkonst :: Sing s -> Scalar t -> t s
    tkonst s x = gen s $ \_ -> x

    tsum :: SingI s => t s -> Scalar t
    tmap :: SingI s => (Scalar t -> Scalar t) -> t s -> t s
    tmap f x = tzipN (\case I x' :* ØV -> f x') (x :* ØV)

    tzip
        :: SingI s
        => (Scalar t -> Scalar t -> Scalar t)
        -> t s
        -> t s
        -> t s
    tzip f x y = tzipN (\case I x' :* I y' :* ØV -> f x' y') (x :* y :* ØV)

    tzipN
        :: SingI s
        => (Vec n (Scalar t) -> Scalar t)
        -> VecT n t s
        -> t s
    tzipN f xs = gen sing $ \i ->
        f $ vmap (I . tindex i) xs

    tsize
        :: SingI s
        => t s
        -> Int

    tindex
        :: SingI s
        => Prod Finite s
        -> t s
        -> Scalar t

    {-# MINIMAL genA, tsum, tsize, tindex #-}

fromScalar :: Tensor t => Scalar t -> t '[]
fromScalar x = gen SNil (\_ -> x)

toScalar :: Tensor t => t '[] -> Scalar t
toScalar = tindex Ø

tmapOp
    :: (Tensor t, SingI s)
    => (forall q. AD q (Forward (Scalar t)) -> AD q (Forward (Scalar t)))
    -> Op '[t s] '[t s]
tmapOp f = op1' $ \x ->
    let y  = tmap (fst . diff' f) x
        dy = tmap (diff f) x
    in  (only_ y, maybe dy (tzip (*) dy) . head')

tzipNOp
    :: forall t s n. (Tensor t, SingI s, Known TCN.Nat n)
    => (forall q. Reifies q Tape => Vec n (Reverse q (Scalar t)) -> Reverse q (Scalar t))
    -> Op (Replicate n (t s)) '[t s]
tzipNOp f = Op $ \xs ->
    let n :: TCN.Nat n
        n = known
        xs' = vmap getI . prodToVec' n $ xs
        y   = tzipN (fst . grad' f) xs'
        dy  = vgen n $ \i -> I $ tzipN (index' i . grad f) xs'
    in  (only_ y, vecToProd . maybe dy (\g -> tzip (*) g <$> dy) . head')

tkonstOp :: forall t s. Tensor t => Sing s -> Op '[Scalar t] '[t s]
tkonstOp s = withSingI s $ op1' $ \x ->
    let res = tkonst s x
    in  (only_ res, maybe (fromIntegral (tsize res)) tsum . head')

tsumOp
    :: forall t s. (Tensor t, SingI s)
    => Op '[ t s ] '[ Scalar t ]
tsumOp = op1' $ \x ->
    ( only_ (tsum x)
    , \case Nothing :< Ø -> tkonst sing 1
            Just g  :< Ø -> tkonst sing g 
    )

scaleOp
    :: forall t s. (Tensor t, SingI s, Num (t s))
    => Op '[ Scalar t, t s ] '[ t s ]
scaleOp = op2' $ \α x ->
    ( only_ (tmap (α *) x)
    , \case Nothing :< Ø -> (tsum x      , tkonst sing α    )
            Just g  :< Ø -> (tsum (x * g), tkonst sing α * g)
    )

oneHot :: (Tensor t, SingI s) => Prod Finite s -> t s
oneHot i = gen sing $ \j -> if i `eq1` j then 1 else 0

