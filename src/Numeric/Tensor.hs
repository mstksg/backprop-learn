{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Numeric.Tensor (
    Tensor(..)
  -- , DoubleProd(..)
  , ProdMap(..)
  , Slice(..)
  , Conv(..)
  , Product, sProduct
  , fromScalar
  , toScalar
  , fromList'
  , fromList
  , convert, convert'
  , tsize
  , tlist
  , tmapOp
  , tzipOp
  , tzipNOp
  , tkonstOp
  , tsumOp
  , scaleOp
  , oneHot
  , Finite
  , range
  ) where

import           Control.Monad.Trans.State.Strict
import           Data.Finite
import           Data.Foldable
import           Data.Kind
import           Data.List
import           Data.Maybe
import           Data.Reflection
import           Data.Singletons.Prelude hiding   (Reverse)
import           Data.Singletons.TypeLits
import           Data.Type.Combinator.Singletons  ()
import           Data.Type.Util
import           Data.Type.Vector hiding          (head')
import           GHC.TypeLits                     as TL
import           Numeric.AD hiding                (Scalar)
import           Numeric.AD.Internal.Reverse
import           Numeric.AD.Mode.Forward          (Forward)
import           Numeric.Backprop.Op
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Family.List hiding          (Reverse)
import           Type.Family.Nat                  (N2)
import qualified Data.Type.Nat                    as TCN
import qualified Data.Vector.Sized                as V

data ProdMap :: (a -> b -> Type) -> [a] -> [b] -> Type where
    PMZ :: ProdMap f '[] '[]
    PMS :: f a b -> ProdMap f as bs -> ProdMap f (a ': as) (b ': bs)

infixr 4 `PMS`

data Slice :: Nat -> Nat -> Type where
    SliceTake   :: Sing c -> Sing r -> Slice (c + r) c
    SliceDrop   :: Sing l -> Sing c -> Slice (l + c) c
    SliceSingle :: Finite c -> Slice c 1
    SliceAll    :: Slice c c
    Slice       :: Sing l -> Sing c -> Sing r -> Slice (l + c + r) c

data Conv :: Nat -> Nat -> Type where
    Conv :: { convMaskDim  :: Sing m
            , convImageDim :: Sing s
            , convStride   :: Finite s
            , convOffset   :: Finite s
            }
         -> Conv m s

class Floating (Scalar t)
        => Tensor (t :: [Nat] -> Type) where
    type Scalar t :: Type

    genA
        :: forall f s. Applicative f
        => Sing s
        -> (Prod Finite s -> f (Scalar t))
        -> f (t s)
    genA s f = withKnownNat (sProduct s) $
      fmap (tload s . fromJust . V.fromList) . traverse f $ range s

    gen :: forall s. Sing s
        -> (Prod Finite s -> Scalar t)
        -> t s
    gen s f = getI $ genA s (I . f)

    tkonst :: Sing s -> Scalar t -> t s
    tkonst s x = gen s (const x)

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

    tindex
        :: SingI s
        => Prod Finite s
        -> t s
        -> Scalar t

    tconv
        :: Sing n
        -> ProdMap Conv m s
        -> t (m >: n)       -- ^ mask
        -> t s              -- ^ tensor
        -> t (s >: n)

    tslice
        :: (SingI n, SingI m)
        => ProdMap Slice n m
        -> t n
        -> t m

    treshape
        :: (SingI s1, Product s1 ~ Product s2)
        => Sing s2
        -> t s1
        -> t s2
    treshape s = tload s . textract

    tload
        :: Sing s
        -> V.Vector (Product s) (Scalar t)
        -> t s
    tload s = fromJust . fromList' s . toList

    textract
        :: SingI s
        => t s
        -> V.Vector (Product s) (Scalar t)
    {-# MINIMAL genA, tsum, tindex, tconv, textract, tslice #-}

tsize :: forall (s :: [Nat]) t. SingI s => t s -> Integer
tsize _ = product (fromSing (sing @[Nat] @s))

range :: Sing ns -> [Prod Finite ns]
range = \case
    SNil            -> [Ø]
    SNat `SCons` ss -> (:<) <$> finites <*> range ss

type family Product (ns :: [Nat]) :: Nat where
    Product '[]       = 1
    Product (n ': ns) = n TL.* (Product ns)

sProduct :: Sing as -> Sing (Product as)
sProduct = \case
    SNil -> SNat
    s `SCons` ss -> s %:* sProduct ss

data DoubleProd :: (k -> Type) -> [k] -> [k] -> Type where
    DPZ :: DoubleProd f '[] '[]
    DPS :: f a -> f b -> DoubleProd f as bs -> DoubleProd f (a ': as) (b ': bs)

instance Known (DoubleProd f '[]) '[] where
    known = DPZ

instance (Known (DoubleProd f as) bs, Known f a, Known f b) => Known (DoubleProd f (a ': as)) (b ': bs) where
    known = DPS known known known

fromScalar :: Tensor t => Scalar t -> t '[]
fromScalar x = gen SNil (\_ -> x)

toScalar :: Tensor t => t '[] -> Scalar t
toScalar = tindex Ø

fromList'
    :: Tensor t
    => Sing s
    -> [Scalar t]
    -> Maybe (t s)
fromList' s = evalStateT . genA s $ \_ -> StateT uncons

fromList
    :: Tensor t
    => Sing s
    -> [Scalar t]
    -> Maybe (t s)
fromList s = case sProduct s of
    SNat -> fmap (tload s) . V.fromList

tlist
    :: (Tensor t, SingI s)
    => t s
    -> [Scalar t]
tlist = toList . textract

tmapOp
    :: (Tensor t, SingI s)
    => (forall q. AD q (Forward (Scalar t)) -> AD q (Forward (Scalar t)))
    -> Op '[t s] '[t s]
tmapOp f = op1' $ \x ->
    let y  = tmap (fst . diff' f) x
        dy = tmap (diff f) x
    in  (only_ y, maybe dy (tzip (*) dy) . head')

tzipOp
    :: forall t s. (Tensor t, SingI s)
    => (forall q. Reifies q Tape => Reverse q (Scalar t) -> Reverse q (Scalar t) -> Reverse q (Scalar t))
    -> Op '[t s, t s] '[t s]
tzipOp f = op2' $ \x y ->
    let f' :: forall q. Reifies q Tape => Vec N2 (Reverse q (Scalar t)) -> Reverse q (Scalar t)
        f' (I x' :* I y' :* ØV) = f x' y'
        z = tzip (\x' y' -> fst $ grad' f' (x' :+ y' :+ ØV)) x y
        g = \case
          Nothing :< Ø ->
            let dx = tzip (\x' y' -> case grad f' (x' :+ y' :+ ØV) of
                                       I dx' :* _ -> dx'
                          ) x y
                dy = tzip (\x' y' -> case grad f' (x' :+ y' :+ ØV) of
                                       _ :* I dy' :* _ -> dy'
                          ) x y
            in  (dx, dy)
          Just dz :< Ø ->
            let dx = tzipN (\(I x' :* I y' :* I d :* ØV) ->
                                case grad f' (x' :+ y' :+ ØV) of
                                  I dx' :* _ :* ØV -> dx' * d
                           ) (x :* y :* dz :* ØV)
                dy = tzipN (\(I x' :* I y' :* I d :* ØV) ->
                                case grad f' (x' :+ y' :+ ØV) of
                                  _ :* I dy' :* ØV -> d * dy'
                           ) (x :* y :* dz :* ØV)
            in  (dx, dy)
    in  (only_ z, g)

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
    in  (only_ res, maybe (fromIntegral (product (fromSing s))) tsum . head')

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

convert'
    :: (Tensor t, Tensor t', SingI ns)
    => (Scalar t -> Scalar t')
    -> t ns
    -> t' ns
convert' f = tload sing . fmap f . textract

convert
    :: (Tensor t, Tensor t', SingI ns, Scalar t ~ Scalar t')
    => t ns
    -> t' ns
convert = convert' id

