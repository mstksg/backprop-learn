{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Data.Type.NonEmpty (
    NETup(..), ToNonEmpty
  , netHead, netTail
  , unNet
  , netT
  , tNet
  ) where

import           Data.Kind
import           Data.List.NonEmpty     (NonEmpty(..))
import           Data.Type.Length
import           Numeric.Backprop.Tuple
import           Type.Class.Known
import           Type.Family.List

data NETup :: NonEmpty Type -> Type where
    NET :: a -> T as -> NETup (a ':| as)

instance (Num a, ListC (Num <$> as), Known Length as) => Num (NETup (a ':| as)) where
    NET x xs + NET y ys = NET (x + y) (xs + ys)
    NET x xs - NET y ys = NET (x - y) (xs - ys)
    NET x xs * NET y ys = NET (x * y) (xs * ys)
    negate (NET x xs)   = NET (negate x) (negate xs)
    abs    (NET x xs)   = NET (abs x   ) (abs xs   )
    signum (NET x xs)   = NET (signum x) (signum xs)
    fromInteger x       = NET (fromInteger x) (fromInteger x)

netHead :: Functor f => (a -> f b) -> NETup (a ':| as) -> f (NETup (b ':| as))
netHead f (NET x xs) = (`NET` xs) <$> f x

netTail :: Functor f => (T as -> f (T bs)) -> NETup (a ':| as) -> f (NETup (a ':| bs))
netTail f (NET x xs) = NET x <$> f xs

unNet :: NETup (a ':| as) -> (a, T as)
unNet (NET x xs) = (x, xs)

netT :: NETup (a ':| as) -> T (a ': as)
netT (NET x xs) = x :& xs

tNet :: T (a ': as) -> NETup (a ':| as)
tNet (x :& xs) = NET x xs

type family ToNonEmpty (l :: [k]) = (m :: Maybe (NonEmpty k)) | m -> l where
    ToNonEmpty '[]       = 'Nothing
    ToNonEmpty (a ': as) = 'Just (a ':| as)

