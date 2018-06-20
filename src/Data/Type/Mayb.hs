{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
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
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Data.Type.Mayb (
    MaybeC, MaybeToList, ListToMaybe
  , Mayb(.., J_I), fromJ_, maybToList, listToMayb
  , P(..), KnownMayb, knownMayb
  , zipMayb
  , zipMayb3
  , FromJust
  , MaybeWit(..), type (<$>)
  , type (:&?), pattern (:&?), splitTupMaybe, tupMaybe
  , BoolMayb, boolMayb
  , pattern MaybB
  ) where

import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Boolean
import           Data.Type.Combinator
import           Data.Type.Product
import           Data.Type.Tuple
import           Numeric.Backprop
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.Maybe    (type (<$>))
import qualified GHC.TypeLits         as TL

type family MaybeC (c :: k -> Constraint) (m :: Maybe k) :: Constraint where
    MaybeC c ('Just a) = c a
    MaybeC c 'Nothing  = ()

type family MaybeToList (m :: Maybe k) = (l :: [k]) | l -> m where
    MaybeToList 'Nothing  = '[]
    MaybeToList ('Just a) = '[a]

-- type family ConsMaybe (ml :: (Maybe k, [k])) = (l :: (Bool, [k])) | l -> ml where
--     ConsMaybe '( 'Nothing, as) = '( 'False, as      )
--     ConsMaybe '( 'Just a , as) = '( 'True , a ': as )

maybToList
    :: Mayb f m
    -> Prod f (MaybeToList m)
maybToList N_     = Ø
maybToList (J_ x) = x :< Ø

type family ListToMaybe (l :: [k]) :: Maybe k where
    ListToMaybe '[]       = 'Nothing
    ListToMaybe (a ': as) = 'Just a

listToMayb
    :: Prod f as
    -> Mayb f (ListToMaybe as)
listToMayb Ø        = N_
listToMayb (x :< _) = J_ x

class MaybeWit (c :: k -> Constraint) (m :: Maybe k) where
    maybeWit :: Mayb (Wit1 c) m

instance (MaybeC c m, Known (Mayb P) m) => MaybeWit c m where
    maybeWit = case known @_ @(Mayb P) @m of
        J_ _ -> J_ Wit1
        N_   -> N_

type KnownMayb = Known (Mayb P)

knownMayb :: KnownMayb p => Mayb P p
knownMayb = known

data Mayb :: (k -> Type) -> Maybe k -> Type where
    N_ :: Mayb f 'Nothing
    J_ :: !(f a) -> Mayb f ('Just a)

deriving instance MaybeC Show (f <$> m) => Show (Mayb f m)

data P :: k -> Type where
    P :: P a

fromJ_ :: Mayb f ('Just a) -> f a
fromJ_ (J_ x) = x

pattern J_I :: a -> Mayb I ('Just a)
pattern J_I x = J_ (I x)

instance Known P k where
    known = P

instance Known (Mayb f) 'Nothing where
    known = N_

instance Known f a => Known (Mayb f) ('Just a) where
    type KnownC (Mayb f) ('Just a) = Known f a
    known = J_ known

instance Functor1 Mayb where
    map1 f (J_ x) = J_ (f x)
    map1 _ N_     = N_

zipMayb
    :: (forall a. f a -> g a -> h a)
    -> Mayb f m
    -> Mayb g m
    -> Mayb h m
zipMayb f (J_ x) (J_ y) = J_ (f x y)
zipMayb _ N_     N_     = N_

zipMayb3
    :: (forall a. f a -> g a -> h a -> i a)
    -> Mayb f m
    -> Mayb g m
    -> Mayb h m
    -> Mayb i m
zipMayb3 f (J_ x) (J_ y) (J_ z) = J_ (f x y z)
zipMayb3 _ N_     N_     N_ = N_

m2  :: forall c f m. MaybeC c (f <$> m)
    => (forall a. c (f a) => f a -> f a -> f a)
    -> Mayb f m
    -> Mayb f m
    -> Mayb f m
m2 f (J_ x) (J_ y) = J_ (f x y)
m2 _ N_     N_     = N_

m1  :: forall c f m. MaybeC c (f <$> m)
    => (forall a. c (f a) => f a -> f a)
    -> Mayb f m
    -> Mayb f m
m1 f (J_ x) = J_ (f x)
m1 _ N_     = N_

m0  :: forall c f m. (MaybeC c (f <$> m))
    => (forall a. c (f a) => f a)
    -> Mayb P m
    -> Mayb f m
m0 x (J_ _) = J_ x
m0 _ N_     = N_

instance (Known (Mayb P) m, MaybeC Num (f <$> m)) => Num (Mayb f m) where
    (+) = m2 @Num (+)
    (-) = m2 @Num (-)
    (*) = m2 @Num (*)
    negate = m1 @Num negate
    abs    = m1 @Num abs
    signum = m1 @Num signum
    fromInteger x = m0 @Num (fromInteger x) known

instance (Known (Mayb P) m, MaybeC Num (f <$> m), MaybeC Fractional (f <$> m))
      => Fractional (Mayb f m) where
    (/) = m2 @Fractional (/)
    recip = m1 @Fractional recip
    fromRational x = m0 @Fractional (fromRational x) known

type family FromJust (d :: TL.ErrorMessage) (m :: Maybe k) :: k where
    FromJust e ('Just a) = a
    FromJust e 'Nothing  = TL.TypeError e

type family (a :: Maybe Type) :&? (b :: Maybe Type) :: Maybe Type where
    'Nothing :&? 'Nothing = 'Nothing
    'Nothing :&? 'Just b  = 'Just b
    'Just a  :&? 'Nothing = 'Just a
    'Just a  :&? 'Just b  = 'Just (a :& b)
infixr 1 :&?

pattern (:&?)
    :: (MaybeC Backprop a, MaybeC Backprop b, KnownMayb a, KnownMayb b, Reifies s W)
    => Mayb (BVar s) a
    -> Mayb (BVar s) b
    -> Mayb (BVar s) (a :&? b)
pattern x :&? y <- (splitTupMaybe (\(v :&& u) -> (v, u))->(x, y))
  where
    (:&?) = tupMaybe (:&&)

tupMaybe
    :: forall f a b. ()
    => (forall a' b'. (a ~ 'Just a', b ~ 'Just b') => f a' -> f b' -> f (a' :& b'))
    -> Mayb f a
    -> Mayb f b
    -> Mayb f (a :&? b)
tupMaybe f = \case
    N_   -> \case
      N_   -> N_
      J_ y -> J_ y
    J_ x -> \case
      N_   -> J_ x
      J_ y -> J_ (f x y)

splitTupMaybe
    :: forall f a b. (KnownMayb a, KnownMayb b)
    => (forall a' b'. (a ~ 'Just a', b ~ 'Just b') => f (a' :& b') -> (f a', f b'))
    -> Mayb f (a :&? b)
    -> (Mayb f a, Mayb f b)
splitTupMaybe f = case knownMayb @a of
    N_ -> case knownMayb @b of
      N_ -> \case
        N_ -> (N_, N_)
      J_ _ -> \case
        J_ y -> (N_, J_ y)
    J_ _ -> case knownMayb @b of
      N_ -> \case
        J_ x -> (J_ x, N_)
      J_ _ -> \case
        J_ xy -> bimap J_ J_ . f $ xy

type family BoolMayb (b :: Bool) = (m :: Maybe ()) | m -> b where
    BoolMayb 'False = 'Nothing
    BoolMayb 'True  = 'Just '()

boolMayb :: Boolean b -> Mayb P (BoolMayb b)
boolMayb False_ = N_
boolMayb True_  = J_ P

instance MaybeC Backprop (f <$> a) => Backprop (Mayb f a) where
    zero = \case
      N_ -> N_
      J_ x  -> J_ (zero x)
    {-# INLINE zero #-}
    add = \case
      N_ -> \case
        N_ -> N_
      J_ x -> \case
        J_ y -> J_ (add x y)
    {-# INLINE add #-}
    one = \case
      N_ -> N_
      J_ x  -> J_ (one x)
    {-# INLINE one #-}

pattern MaybB
    :: (Reifies s W, MaybeC Backprop a, KnownMayb a)
    => Mayb (BVar s) a
    -> BVar s (Mayb I a)
pattern MaybB v <- (_mb->v)
  where
    MaybB = \case
      N_   -> auto N_
      J_ x -> isoVar (J_ . I) (getI . fromJ_) x
{-# COMPLETE MaybB #-}

_mb :: forall a s. (MaybeC Backprop a, KnownMayb a, Reifies s W)
    => BVar s (Mayb I a)
    -> Mayb (BVar s) a
_mb v = case knownMayb @a of
          J_ _ -> J_ $ isoVar (getI . fromJ_) (J_ . I) v
          N_   -> N_
{-# INLINE _mb #-}

deriving instance Backprop a => Backprop (I a)
