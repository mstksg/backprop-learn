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
    -- MaybeC
    -- , MaybeToList, ListToMaybe
  -- , Mayb(.., J_I), fromJ_
    PMaybe(..,PJustI), fromPJust
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

data P :: k -> Type where
    P :: P a

fromPJust :: PMaybe f ('Just a) -> f a
fromPJust (PJust x) = x

pattern PJustI :: a -> PMaybe Identity ('Just a)
pattern PJustI x = PJust (Identity x)


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
    :: (Reifies s W, AllConstrainedProd Backprop a, SingI a, PureProd Maybe a)
    => PMaybe (BVar s) a
    -> BVar s (PMaybe Identity a)
pattern MaybB v <- (_mb->v)
  where
    MaybB = \case
      PNothing -> auto PNothing
      PJust x  -> isoVar (PJust . Identity) (runIdentity . fromPJust) x
{-# COMPLETE MaybB #-}

_mb :: forall a s. (AllConstrainedProd Backprop a, PureProd Maybe a, Reifies s W)
    => BVar s (PMaybe Identity a)
    -> PMaybe (BVar s) a
_mb v = case pureShape @_ @a of
    PJust _  -> PJust $ isoVar (runIdentity . fromPJust) (PJust . Identity) v
    PNothing -> PNothing
{-# INLINE _mb #-}
