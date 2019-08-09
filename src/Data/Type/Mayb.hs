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
    MaybeC
    -- , MaybeToList, ListToMaybe
  -- , Mayb(.., J_I), fromJ_
  , PMaybe(..,PJustI), fromPJust
  , maybToList, listToMayb
  -- , P(..), KnownMayb, knownMayb
  -- , zipMayb
  -- , zipMayb3
  -- , FromJust
  -- , MaybeWit(..), type (<$>)
  , type (:#?), pattern (:#?), splitTupMaybe, tupMaybe
  , BoolMayb, boolMayb
  , pattern MaybB
  ) where

import           Data.Bifunctor
import           Data.Functor.Identity
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.Bool
import           Data.Singletons.Prelude.Maybe
import           Data.Type.Functor.Product
import           Data.Type.Tuple
import           Data.Vinyl
import           Numeric.Backprop
import qualified Data.Vinyl.Functor            as V
import qualified Data.Vinyl.TypeLevel          as V

type MaybeC c m = V.AllConstrained c (MaybeToList m)

-- type family MaybeC (c :: k -> Constraint) (m :: Maybe k) :: Constraint where
--     MaybeC c ('Just a) = c a
--     MaybeC c 'Nothing  = ()

-- type family KnownMayb (m :: Maybe k) :: Constraint where


-- type family MaybeToList (m :: Maybe k) = (l :: [k]) | l -> m where
--     MaybeToList 'Nothing  = '[]
--     MaybeToList ('Just a) = '[a]

-- type family ConsMaybe (ml :: (Maybe k, [k])) = (l :: (Bool, [k])) | l -> ml where
--     ConsMaybe '( 'Nothing, as) = '( 'False, as      )
--     ConsMaybe '( 'Just a , as) = '( 'True , a ': as )

maybToList
    :: PMaybe f m
    -> Rec f (MaybeToList m)
maybToList PNothing  = RNil
maybToList (PJust x) = x :& RNil

listToMayb
    :: Rec f as
    -> PMaybe f (ListToMaybe as)
listToMayb RNil     = PNothing
listToMayb (x :& _) = PJust x

-- class MaybeWit (c :: k -> Constraint) (m :: Maybe k) where
--     maybeWit :: Mayb (Wit1 c) m

-- instance (MaybeC c m, Known (Mayb P) m) => MaybeWit c m where
--     maybeWit = case known @_ @(Mayb P) @m of
--         PJust _ -> PJust Wit1
--         PNothing   -> PNothing

-- type KnownMayb = Known (Mayb P)

-- knownMayb :: KnownMayb p => PMaybe P p
-- knownMayb = known

-- data Mayb :: (k -> Type) -> Maybe k -> Type where
--     PNothing :: Mayb f 'Nothing
--     J_ :: !(f a) -> Mayb f ('Just a)

-- deriving instance MaybeC Show (f <$> m) => Show (Mayb f m)

data P :: k -> Type where
    P :: P a

fromPJust :: PMaybe f ('Just a) -> f a
fromPJust (PJust x) = x

pattern PJustI :: a -> PMaybe Identity ('Just a)
pattern PJustI x = PJust (Identity x)

-- instance Known P k where
--     known = P

-- instance Known (Mayb f) 'Nothing where
--     known = PNothing

-- instance Known f a => Known (Mayb f) ('Just a) where
--     type KnownC (Mayb f) ('Just a) = Known f a
--     known = PJust known

-- instance Functor1 Mayb where
--     map1 f (PJust x) = PJust (f x)
--     map1 _ PNothing     = PNothing

-- zipMayb
--     :: (forall a. f a -> g a -> h a)
--     -> Mayb f m
--     -> Mayb g m
--     -> Mayb h m
-- zipMayb f (PJust x) (PJust y) = PJust (f x y)
-- zipMayb _ PNothing     PNothing     = PNothing

-- zipMayb3
--     :: (forall a. f a -> g a -> h a -> i a)
--     -> Mayb f m
--     -> Mayb g m
--     -> Mayb h m
--     -> Mayb i m
-- zipMayb3 f (PJust x) (PJust y) (PJust z) = PJust (f x y z)
-- zipMayb3 _ PNothing     PNothing     PNothing = PNothing

-- m2  :: forall c f m. MaybeC c (f <$> m)
--     => (forall a. c (f a) => f a -> f a -> f a)
--     -> PMaybe f m
--     -> PMaybe f m
--     -> PMaybe f m
-- m2 f (PJust x) (PJust y) = PJust (f x y)
-- m2 _ PNothing     PNothing     = PNothing

-- m1  :: forall c f m. MaybeC c (f <$> m)
--     => (forall a. c (f a) => f a -> f a)
--     -> Mayb f m
--     -> Mayb f m
-- m1 f (PJust x) = PJust (f x)
-- m1 _ PNothing     = PNothing

-- m0  :: forall c f m. (MaybeC c (f <$> m))
--     => (forall a. c (f a) => f a)
--     -> PMaybe P m
--     -> PMaybe f m
-- m0 x (PJust _) = PJust x
-- m0 _ PNothing     = PNothing

-- instance (Known (Mayb P) m, MaybeC Num (f <$> m)) => Num (Mayb f m) where
--     (+) = m2 @Num (+)
--     (-) = m2 @Num (-)
--     (*) = m2 @Num (*)
--     negate = m1 @Num negate
--     abs    = m1 @Num abs
--     signum = m1 @Num signum
--     fromInteger x = m0 @Num (fromInteger x) known

-- instance (Known (Mayb P) m, MaybeC Num (f <$> m), MaybeC Fractional (f <$> m))
--       => Fractional (Mayb f m) where
--     (/) = m2 @Fractional (/)
--     recip = m1 @Fractional recip
--     fromRational x = m0 @Fractional (fromRational x) known

-- type family FromJust (d :: TL.ErrorMessage) (m :: Maybe k) :: k where
--     FromJust e ('Just a) = a
--     FromJust e 'Nothing  = TL.TypeError e

type family (a :: Maybe Type) :#? (b :: Maybe Type) :: Maybe Type where
    'Nothing :#? 'Nothing = 'Nothing
    'Nothing :#? 'Just b  = 'Just b
    'Just a  :#? 'Nothing = 'Just a
    'Just a  :#? 'Just b  = 'Just (a :# b)
infixr 1 :#?

pattern (:#?)
    :: (MaybeC Backprop a, MaybeC Backprop b, Reifies s W, PureProd Maybe a, PureProd Maybe b)
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

type family BoolMayb (b :: Bool) = (m :: Maybe ()) | m -> b where
    BoolMayb 'False = 'Nothing
    BoolMayb 'True  = 'Just '()

boolMayb :: Sing b -> PMaybe P (BoolMayb b)
boolMayb SFalse = PNothing
boolMayb STrue  = PJust P

instance ReifyConstraintProd Maybe Backprop f as => Backprop (PMaybe f as) where
    zero = mapProd (\(V.Compose (Dict x)) -> zero x)
         . reifyConstraintProd @_ @Backprop
    {-# INLINE zero #-}
    add xs = zipWithProd (\x (V.Compose (Dict y)) -> add x y) xs
           . reifyConstraintProd @_ @Backprop
    {-# INLINE add #-}
    one  = mapProd (\(V.Compose (Dict x)) -> one x)
         . reifyConstraintProd @_ @Backprop
    {-# INLINE one #-}

pattern MaybB
    :: (Reifies s W, MaybeC Backprop a, SingI a, PureProd Maybe a)
    => PMaybe (BVar s) a
    -> BVar s (PMaybe Identity a)
pattern MaybB v <- (_mb->v)
  where
    MaybB = \case
      PNothing -> auto PNothing
      PJust x  -> isoVar (PJust . Identity) (runIdentity . fromPJust) x
{-# COMPLETE MaybB #-}

_mb :: forall a s. (MaybeC Backprop a, PureProd Maybe a, Reifies s W)
    => BVar s (PMaybe Identity a)
    -> PMaybe (BVar s) a
_mb v = case pureShape @_ @a of
    PJust _  -> PJust $ isoVar (runIdentity . fromPJust) (PJust . Identity) v
    PNothing -> PNothing
{-# INLINE _mb #-}

-- deriving instance Backprop a => Backprop (I a)
