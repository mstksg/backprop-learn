{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Type.Mayb (
    MaybeC, MaybeToList, ListToMaybe
  , Mayb(.., J_I), fromJ_, maybToList, listToMayb
  , P(..), KnownMayb, knownMayb
  , zipMayb
  , zipMayb3
  , FromJust
  , MaybeWit(..), type (<$>)
  ) where

import           Data.Kind
import           Data.Type.Combinator
import           Data.Type.Product
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import qualified GHC.TypeLits         as TL

type family MaybeC (c :: k -> Constraint) (m :: Maybe k) :: Constraint where
    MaybeC c ('Just a) = c a
    MaybeC c 'Nothing  = ()

type family (<$>) (f :: k -> j) (m :: Maybe k) :: Maybe j where
    f <$> 'Just a  = 'Just (f a)
    f <$> 'Nothing = 'Nothing

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
    J_ :: f a -> Mayb f ('Just a)

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

