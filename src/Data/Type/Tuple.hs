{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

-- |
-- Module      : Data.Type.Tuple
-- Copyright   : (c) Justin Le 2018
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- If you are writing a library that needs to export 'BVar's of tuples,
-- consider using the tuples in this module so that your library can have
-- easy interoperability with other libraries using /backprop/.
--
-- Because of API decisions, 'backprop' and 'gradBP' only work with things
-- with 'Num' instances.  However, this disallows default 'Prelude' tuples
-- (without orphan instances from packages like
-- <https://hackage.haskell.org/package/NumInstances NumInstances>).
--
-- Until tuples have 'Num' instances in /base/, this module is intended to
-- be a workaround for situations where:
--
-- This comes up often in cases where:
--
--     (1) A function wants to return more than one value (@'BVar' s ('T2'
--     a b)@
--     (2) You want to uncurry a 'BVar' function to use with 'backprop' and
--     'gradBP'.
--     (3) You want to use the useful 'Prism's automatically generated by
--     the lens library, which use tuples for multiple-constructor fields.
--
-- Only 2-tuples and 3-tuples are provided.  Any more and you should
-- probably be using your own custom product types, with instances
-- automatically generated from something like
-- <https://hackage.haskell.org/package/one-liner-instances one-liner-instances>.
--
-- Lenses into the fields are provided, but they also work with '_1', '_2',
-- and '_3' from "Lens.Micro".  However, note that these are incompatible
-- with '_1', '_2', and '_3' from "Control.Lens".
--
-- You can "construct" a @'BVar' s ('T2' a b)@ with functions like
-- 'isoVar'.
--
-- @since 0.1.1.0
--


module Data.Type.Tuple (
  -- * Zero-tuples (unit)
    T0(..)
  -- * Two-tuples
  , (:#)(..), pattern (:##)
  -- ** Conversions
  -- $t2iso
  , t2Tup, tupT2
  -- ** Consumption
  , uncurryT2, curryT2
  -- ** Lenses
  , t2_1, t2_2
  -- * N-Tuples
  , T, TF(..), pattern (:&&)
  , indexT
  -- ** Conversions
  -- -- $tiso
  , tOnly, onlyT
  -- , tSplit, tAppend
  -- , tProd, prodT
  -- ** Lenses
  -- , tIx
  , tHead
  , tTail
  -- * Maybe
  , TMaybe
  , PMaybe(..,TJust), fromPJust
  , type (:#?), pattern (:#?), splitTupMaybe, tupMaybe
  , pattern MaybB
  ) where

import           Control.DeepSeq
import           Data.Bifunctor
import           Data.Coerce
import           Data.Data
import           Data.Kind
import           Data.Profunctor hiding     (rmap)
import           Data.Semigroup
import           Data.Type.Functor.Product
import           Data.Vinyl.Core
import           GHC.Generics               ((:*:)(..))
import           GHC.Generics               (Generic)
import           Lens.Micro
import           Lens.Micro.Internal hiding (Index)
import           Numeric.Backprop hiding    (T2)
import           Numeric.Opto.Ref
import           Numeric.Opto.Update
import qualified Data.Binary                as Bi
import qualified Data.Functor.Contravariant as Co
import qualified Data.Vinyl.Functor         as V

-- | Unit ('()') with 'Num', 'Fractional', and 'Floating' instances.
--
-- Be aware that the methods in its numerical instances are all non-strict:
--
-- @
-- _ + _ = 'T0'
-- 'negate' _ = 'T0'
-- 'fromIntegral' _ = 'T0'
-- @
--
-- @since 0.1.4.0
data T0 = T0
  deriving (Show, Read, Eq, Ord, Generic, Data)

-- | Strict 2-tuple with 'Num', 'Fractional', and 'Floating' instances.
--
-- @since 0.1.1.0
data a :# b = !a :# !b
  deriving (Show, Read, Eq, Ord, Generic, Functor, Data, Typeable)
infixr 1 :#

-- | Strict inductive N-tuple with a 'Num', 'Fractional', and 'Floating'
-- instances.
--
-- It is basically "yet another HList", like the one found in
-- "Data.Type.Product" and many other locations on the haskell ecosystem.
-- Because it's inductively defined, it has O(n) random indexing, but is
-- efficient for zipping and mapping and other sequential consumption
-- patterns.
--
-- It is provided because of its 'Num' instance, making it useful for
-- /backproup/.  Will be obsolete when 'Data.Type.Product.Product' gets
-- numerical instances.
--
-- @since 0.1.5.0
type T = Rec TF

newtype TF a = TF { getTF :: a }
  deriving (Show, Eq, Ord, Num, Fractional, Floating, Backprop, Generic, Typeable, NFData)

type TMaybe = PMaybe TF

_TF :: (Profunctor p, Functor f) => p a (f b) -> p (TF a) (f (TF b))
_TF = dimap getTF (fmap TF)

pattern (:&&) :: a -> T as -> T (a ': as)
pattern x :&& xs = TF x :& xs
{-# COMPLETE (:&&) #-}

infixr 5 :&&

-- | @since 0.1.5.1
deriving instance Typeable T0
-- | @since 0.1.5.1
deriving instance Typeable (a :# b)

instance NFData T0
instance (NFData a, NFData b) => NFData (a :# b)

-- TODO: optimize

-- | @since 0.1.5.1
instance Bi.Binary T0
-- | @since 0.1.5.1
instance (Bi.Binary a, Bi.Binary b) => Bi.Binary (a :# b)
instance Bi.Binary a => Bi.Binary (TF a)

instance Bifunctor (:#) where
    bimap f g (x :# y) = f x :# g y

-- | Convert to a Haskell tuple.
--
-- Forms an isomorphism with 'tupT2'.
t2Tup :: (a :# b) -> (a, b)
t2Tup (x :# y) = (x, y)

-- | Convert from Haskell tuple.
--
-- Forms an isomorphism with 't2Tup'.
tupT2 :: (a, b) -> a :# b
tupT2 (x, y) = x :# y

-- | A singleton 'T'
--
-- Forms an isomorphism with 'tOnly'
--
-- @since 0.1.5.0
onlyT :: a -> T '[a]
onlyT = (:& RNil) . TF

-- | Extract a singleton 'T'
--
-- Forms an isomorphism with 'onlyT'
--
-- @since 0.1.5.0
tOnly :: T '[a] -> a
tOnly (TF x :& _) = x

-- | Uncurry a function to take in a 'T2' of its arguments
--
-- @since 0.1.2.0
uncurryT2 :: (a -> b -> c) -> a :# b -> c
uncurryT2 f (x :# y) = f x y

-- | Curry a function taking a 'T2' of its arguments
--
-- @since 0.1.2.0
curryT2 :: (a :# b -> c) -> a -> b -> c
curryT2 f x y = f (x :# y)

instance Field1 (a :# b) (a' :# b) a a' where
    _1 = t2_1

instance Field2 (a :# b) (a :# b') b b' where
    _2 = t2_2

instance Field1 (T (a ': as)) (T (a ': as)) a a where
    _1 = tIx IZ

instance Field2 (T (a ': b ': as)) (T (a ': b ': as)) b b where
    _2 = tIx (IS IZ)

instance Field3 (T (a ': b ': c ': as)) (T (a ': b ': c ': as)) c c where
    _3 = tIx (IS (IS IZ))

-- | Lens into the first field of a 'T2'.  Also exported as '_1' from
-- "Lens.Micro".
t2_1 :: Lens (a :# b) (a' :# b) a a'
t2_1 f (x :# y) = (:# y) <$> f x

-- | Lens into the second field of a 'T2'.  Also exported as '_2' from
-- "Lens.Micro".
t2_2 :: Lens (a :# b) (a :# b') b b'
t2_2 f (x :# y) = (x :#) <$> f y

-- | Index into a 'T'.
--
-- /O(i)/
--
-- @since 0.1.5.0
indexT :: Index as a -> T as -> a
indexT = flip (^.) . tIx


recIx :: forall f as a. Index as a -> Lens' (Rec f as) (f a)
recIx = \case
    IZ   -> \f -> \case
      x :& xs -> (:& xs) <$> f x
    IS i -> \f -> \case
      x :& xs -> (x :&) <$> recIx i f xs

-- | Lens into a given index of a 'T'.
--
-- @since 0.1.5.0
tIx :: Index as a -> Lens' (T as) a
tIx i = recIx i . _TF

-- | Lens into the head of a 'T'
--
-- @since 0.1.5.0
tHead :: Lens (T (a ': as)) (T (b ': as)) a b
tHead f (TF x :& xs) = (:& xs) . TF <$> f x

-- | Lens into the tail of a 'T'
--
-- @since 0.1.5.0
tTail :: Lens (T (a ': as)) (T (a ': bs)) (T as) (T bs)
tTail f (x :& xs) = (x :&) <$> f xs

instance Num T0 where
    _ + _         = T0
    _ - _         = T0
    _ * _         = T0
    negate _      = T0
    abs    _      = T0
    signum _      = T0
    fromInteger _ = T0

instance Fractional T0 where
    _ / _          = T0
    recip _        = T0
    fromRational _ = T0

instance Floating T0 where
    pi          = T0
    _ ** _      = T0
    logBase _ _ = T0
    exp   _     = T0
    log   _     = T0
    sqrt  _     = T0
    sin   _     = T0
    cos   _     = T0
    asin  _     = T0
    acos  _     = T0
    atan  _     = T0
    sinh  _     = T0
    cosh  _     = T0
    asinh _     = T0
    acosh _     = T0
    atanh _     = T0

instance Semigroup T0 where
    _ <> _ = T0

instance Monoid T0 where
    mempty = T0
    mappend = (<>)

instance (Num a, Num b) => Num (a :# b) where
    (x1 :# y1) + (x2 :# y2) = x1 + x2 :# y1 + y2
    (x1 :# y1) - (x2 :# y2) = x1 - x2 :# y1 - y2
    (x1 :# y1) * (x2 :# y2) = x1 * x2 :# y1 * y2
    negate (x :# y)     = negate x :# negate y
    abs    (x :# y)     = abs    x :# abs    y
    signum (x :# y)     = signum x :# signum y
    fromInteger x       = fromInteger x :# fromInteger x

instance (Fractional a, Fractional b) => Fractional (a :# b) where
    (x1 :# y1) / (x2 :# y2) = x1 / x2 :# y1 / y2
    recip (x :# y)          = recip x :# recip y
    fromRational x          = fromRational x :# fromRational x

instance (Floating a, Floating b) => Floating (a :# b) where
    pi                            = pi :# pi
    (x1 :# y1) ** (x2 :# y2)      = x1 ** x2 :# y1 ** y2
    logBase (x1 :# y1) (x2 :# y2) = logBase x1 x2 :# logBase y1 y2
    exp   (x :# y)                = exp   x :# exp   y
    log   (x :# y)                = log   x :# log   y
    sqrt  (x :# y)                = sqrt  x :# sqrt  y
    sin   (x :# y)                = sin   x :# sin   y
    cos   (x :# y)                = cos   x :# cos   y
    asin  (x :# y)                = asin  x :# asin  y
    acos  (x :# y)                = acos  x :# acos  y
    atan  (x :# y)                = atan  x :# atan  y
    sinh  (x :# y)                = sinh  x :# sinh  y
    cosh  (x :# y)                = cosh  x :# cosh  y
    asinh (x :# y)                = asinh x :# asinh y
    acosh (x :# y)                = acosh x :# acosh y
    atanh (x :# y)                = atanh x :# atanh y

instance (Semigroup a, Semigroup b) => Semigroup (a :# b) where
    (x1 :# y1) <> (x2 :# y2) = x1 <> x2 :# y1 <> y2

instance (Semigroup a, Semigroup b, Monoid a, Monoid b) => Monoid (a :# b) where
    mappend = (<>)
    mempty  = mempty :# mempty

-- | Initialize a 'T' with a Rank-N value.  Mostly used internally, but
-- provided in case useful.
--
-- Must be used with /TypeApplications/ to provide the Rank-N constraint.
--
-- @since 0.1.5.0
constT
    :: forall c as. RPureConstrained c as
    => (forall a. c a => a)
    -> T as
constT x = rpureConstrained @c (TF x)

-- | Map over a 'T' with a Rank-N function.  Mostly used internally, but
-- provided in case useful.
--
-- Must be used with /TypeApplications/ to provide the Rank-N constraint.
--
-- @since 0.1.5.0
mapT
    :: forall c as. (RPureConstrained c as, RMap as, RApply as)
    => (forall a. c a => a -> a)
    -> T as
    -> T as
mapT f = rzipWith coerce (rpureConstrained @c @as @Endo (Endo f))
  -- where
  --   go :: forall bs. ListC (c <$> bs) => T bs -> T bs
  --   go TNil      = TNil
  --   go (x :# xs) = f x :# go xs

-- | Map over a 'T' with a Rank-N function.  Mostly used internally, but
-- provided in case useful.
--
-- Must be used with /TypeApplications/ to provide the Rank-N constraint.
--
-- @since 0.1.5.0
zipT
    :: forall c as. (RPureConstrained c as, RMap as, RApply as)
    => (forall a. c a => a -> a -> a)
    -> T as
    -> T as
    -> T as
zipT f = rapply . rzipWith coerce (rpureConstrained @c @as @TripleEndo (TE f))

newtype TripleEndo a = TE (a -> a -> a)

instance (RPureConstrained Num as, RMap as, RApply as) => Num (Rec TF as) where
    (+)           = zipT @Num (+)
    (-)           = zipT @Num (-)
    (*)           = zipT @Num (*)
    negate        = mapT @Num negate
    abs           = mapT @Num abs
    signum        = mapT @Num signum
    fromInteger x = constT @Num (fromInteger x)

instance (RPureConstrained Num as, RPureConstrained Fractional as, RMap as, RApply as) => Fractional (T as) where
    (/)            = zipT @Fractional (/)
    recip          = mapT @Fractional recip
    fromRational x = constT @Fractional (fromRational x)

instance (RPureConstrained Num as, RPureConstrained Fractional as, RPureConstrained Floating as, RMap as, RApply as) => Floating (T as) where
    pi      = constT @Floating pi
    (**)    = zipT @Floating (**)
    logBase = zipT @Floating logBase
    exp     = mapT @Floating exp
    log     = mapT @Floating log
    sqrt    = mapT @Floating sqrt
    sin     = mapT @Floating sin
    cos     = mapT @Floating cos
    asin    = mapT @Floating asin
    acos    = mapT @Floating acos
    atan    = mapT @Floating atan
    sinh    = mapT @Floating sinh
    cosh    = mapT @Floating cosh
    asinh   = mapT @Floating asinh
    acosh   = mapT @Floating acosh
    atanh   = mapT @Floating atanh

instance (Backprop a, Backprop b) => Backprop (a :# b) where
    zero (x :# y) = zero x :# zero y
    add (x1 :# y1) (x2 :# y2) = add x1 x2 :# add y1 y2
    one (x :# y) = one x :# one y

pattern (:##)
    :: (Backprop a, Backprop b, Reifies s W)
    => BVar s a
    -> BVar s b
    -> BVar s (a :# b)
pattern x :## y <- (\xy -> (xy ^^. _1, xy ^^. _2) -> (x, y))
  where
    (:##) = isoVar2 (:#) t2Tup
{-# COMPLETE (:##) #-}

instance (Mutable m a, Mutable m b) => Mutable m (a :# b) where
    type Ref m (a :# b) = GRef m (a :# b)
    thawRef = gThawRef
    freezeRef = gFreezeRef
    copyRef = gCopyRef
instance (Linear c a, Linear c b) => Linear c (a :# b)
instance (Floating c, Ord c, Metric c a, Metric c b) => Metric c (a :# b)
instance (LinearInPlace m c a, LinearInPlace m c b) => LinearInPlace m c (a :# b)


instance RPureConstrained NFData as => NFData (Rec TF as) where
    rnf = go (rpureConstrained @NFData (Co.Op rnf))
      where
        go :: Rec (Co.Op ()) bs -> Rec TF bs -> ()
        go = \case
          RNil -> \case
            RNil -> ()
          Co.Op r :& rs -> \case
            TF x :& xs -> r x `seq` go rs xs

instance (RPureConstrained Bi.Binary as, RMap as, RApply as, RecordToList as) => Bi.Binary (Rec TF as) where
    put = sequence_ @[]
        . recordToList
        . rzipWith (\(Co.Op p) (TF x) -> V.Const (p x))
            (rpureConstrained @Bi.Binary (Co.Op Bi.put))
    get = rtraverse coerce $ rpureConstrained @Bi.Binary Bi.get

instance Mutable m a => Mutable m (TF a) where
    type Ref m (TF a) = TF (Ref m a)

    thawRef = fmap coerce . thawRef @m @a . coerce
    freezeRef = fmap coerce . freezeRef @m @a . coerce
    copyRef v = copyRef @m @a (coerce v) . coerce

instance Linear c a => Linear c (TF a)
instance (Ord c, Floating c, Metric c a) => Metric c (TF a)
instance (Mutable m a, LinearInPlace m c a) => LinearInPlace m c (TF a) where
    TF v .+.= TF x = v .+.= x
    TF v .*= c = v .*= c
    TF v .*+= (c, TF x) = v .*+= (c, x)

fromPJust :: PMaybe f ('Just a) -> f a
fromPJust (PJust x) = x

pattern TJust :: a -> TMaybe ('Just a)
pattern TJust x = PJust (TF x)

type family (a :: Maybe Type) :#? (b :: Maybe Type) :: Maybe Type where
    'Nothing :#? 'Nothing = 'Nothing
    'Nothing :#? 'Just b  = 'Just b
    'Just a  :#? 'Nothing = 'Just a
    'Just a  :#? 'Just b  = 'Just (a :# b)
infixr 1 :#?

pattern (:#?)
    :: (AllConstrainedProd Backprop a, AllConstrainedProd Backprop b, Reifies s W, PureProd Maybe a, PureProd Maybe b)
    => PMaybe (BVar s) a
    -> PMaybe (BVar s) b
    -> PMaybe (BVar s) (a :#? b)
pattern x :#? y <- (splitTupMaybe (\(v :## u) -> (v, u))->(x, y))
  where
    (:#?) = tupMaybe (:##)

tupMaybe
    :: forall f a b. ()
    => (forall a' b'. (a ~ 'Just a', b ~ 'Just b') => f a' -> f b' -> f (a' :# b'))
    -> PMaybe f a
    -> PMaybe f b
    -> PMaybe f (a :#? b)
tupMaybe f = \case
    PNothing   -> \case
      PNothing   -> PNothing
      PJust y -> PJust y
    PJust x -> \case
      PNothing   -> PJust x
      PJust y -> PJust (f x y)

splitTupMaybe
    :: forall f a b. (PureProd Maybe a, PureProd Maybe b)
    => (forall a' b'. (a ~ 'Just a', b ~ 'Just b') => f (a' :# b') -> (f a', f b'))
    -> PMaybe f (a :#? b)
    -> (PMaybe f a, PMaybe f b)
splitTupMaybe f = case pureShape @_ @a of
    PNothing -> case pureShape @_ @b of
      PNothing -> \case
        PNothing -> (PNothing, PNothing)
      PJust _ -> \case
        PJust y -> (PNothing, PJust y)
    PJust _ -> case pureShape @_ @b of
      PNothing -> \case
        PJust x -> (PJust x, PNothing)
      PJust _ -> \case
        PJust xy -> bimap PJust PJust . f $ xy

instance PureProdC Maybe Backprop as => Backprop (TMaybe as) where
    zero   = zipWithProd coerce (pureProdC @_ @Backprop (Endo zero))
    {-# INLINE zero #-}
    add xs = zipWithProd (\a (x :*: y) -> coerce a x y) (pureProdC @_ @Backprop (TE add))
           . zipProd xs
    {-# INLINE add #-}
    one    = zipWithProd coerce (pureProdC @_ @Backprop (Endo one))
    {-# INLINE one #-}

pattern MaybB
    :: (Reifies s W, AllConstrainedProd Backprop a, PureProd Maybe a)
    => PMaybe (BVar s) a
    -> BVar s (TMaybe a)
pattern MaybB v <- (_mb->v)
  where
    MaybB = \case
      PNothing -> auto PNothing
      PJust x  -> isoVar (PJust . TF) (getTF . fromPJust) x
{-# COMPLETE MaybB #-}

_mb :: forall a s. (AllConstrainedProd Backprop a, PureProd Maybe a, Reifies s W)
    => BVar s (TMaybe a)
    -> PMaybe (BVar s) a
_mb v = case pureShape @_ @a of
    PJust _  -> PJust $ isoVar (getTF . fromPJust) (PJust . TF) v
    PNothing -> PNothing
{-# INLINE _mb #-}
