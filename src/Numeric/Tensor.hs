{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}

module Numeric.Tensor (
    Tensor(..)
  ) where

import           Data.Kind
import           Data.Singletons

class SingKind k => Tensor (t :: k -> Type) where
    type IndexT t :: k -> Type
    type ElemT  t :: Type

    genA
        :: Applicative f
        => Sing s
        -> (IndexT t s -> f (ElemT t))
        -> f (t s)

    gen :: Sing s
        -> (IndexT t s -> ElemT t)
        -> t s

    tkonst :: Sing s -> ElemT t -> t s

    tsum :: SingI s => t s -> ElemT t
    tmap :: SingI s => (ElemT t -> ElemT t) -> t s -> t s
    tzip
        :: SingI s
        => (ElemT t -> ElemT t -> ElemT t)
        -> t s
        -> t s
        -> t s

    -- tindex :: IndexT t s -> t s -> ElemT b
    -- tsize :: t s -> IndexT t s


