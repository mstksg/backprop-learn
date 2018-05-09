{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module Data.Type.NonEmpty (
    NETup(.., NETT), ToNonEmpty
  , netHead, netTail
  , unNet
  , netT
  , NonEmpty(..)
  ) where

import           Control.DeepSeq
import           Data.Kind
import           Data.List.NonEmpty   (NonEmpty(..))
import           Data.Type.Combinator
import           Data.Type.Length
import           Data.Type.Product
import           Lens.Micro
import           Numeric.Backprop
import           Numeric.Opto.Ref
import           Numeric.Opto.Update
import           Type.Class.Known
import           Type.Family.List
import qualified Data.Binary          as Bi

-- TODO: num instances, but also maybe generalize to product over functor

data NETup :: NonEmpty Type -> Type where
    NET :: !a -> !(Tuple as) -> NETup (a ':| as)

pattern NETT :: Tuple (a ': as) -> NETup (a ':| as)
pattern NETT { netT } <- (\case NET x xs -> x ::< xs->(!netT))
  where
    NETT (!(x ::< xs)) = NET x xs
{-# COMPLETE NETT #-}

instance (NFData a, ListC (NFData <$> as)) => NFData (NETup (a ':| as)) where
    rnf (NET !x xs) = rnf x `seq` rnfTup xs

rnfTup :: ListC (NFData <$> as) => Tuple as -> ()
rnfTup = \case
    I x :< xs -> rnf x `seq` rnfTup xs
    Ø         -> ()

-- instance (Num a, ListC (Num <$> as), Known Length as) => Num (NETup (a ':| as)) where
--     NETT xs + NETT ys = NETT (xs + ys)
--     NETT xs - NETT ys = NETT (xs - ys)
--     NETT xs * NETT ys = NETT (xs * ys)
--     negate (NETT xs)  = NETT (negate xs)
--     abs (NETT xs)     = NETT (abs xs)
--     signum (NETT xs)  = NETT (signum xs)
--     fromInteger       = NETT . fromInteger

-- instance (Fractional a, ListC (Num <$> as), ListC (Fractional <$> as), Known Length as)
--         => Fractional (NETup (a ':| as)) where
--     NETT xs / NETT ys = NETT (xs / ys)
--     recip (NETT xs)   = NETT (recip xs)
--     fromRational      = NETT . fromRational

-- instance (Floating a, ListC (Num <$> as), ListC (Fractional <$> as), ListC (Floating <$> as), Known Length as)
--         => Floating (NETup (a ':| as)) where
--     pi              = NETT pi
--     sqrt (NETT xs)  = NETT (sqrt xs)
--     exp (NETT xs)   = NETT (exp xs)
--     log (NETT xs)   = NETT (log xs)
--     sin (NETT xs)   = NETT (sin xs)
--     cos (NETT xs)   = NETT (cos xs)
--     tan (NETT xs)   = NETT (tan xs)
--     asin (NETT xs)  = NETT (asin xs)
--     acos (NETT xs)  = NETT (acos xs)
--     atan (NETT xs)  = NETT (atan xs)
--     sinh (NETT xs)  = NETT (sinh xs)
--     cosh (NETT xs)  = NETT (cosh xs)
--     tanh (NETT xs)  = NETT (tanh xs)
--     asinh (NETT xs) = NETT (asinh xs)
--     acosh (NETT xs) = NETT (acosh xs)
--     atanh (NETT xs) = NETT (atanh xs)

instance (Additive a, Additive (Tuple as))
      => Additive (NETup (a ':| as)) where
    NET x xs .+. NET y ys = NET (x .+. y) (xs .+. ys)
    addZero               = NET addZero addZero

instance (Scaling c a, Scaling c (Tuple as)) => Scaling c (NETup (a ':| as)) where
    c .* NET x xs = NET (c .* x) (c .* xs)
    scaleOne      = scaleOne @c @a

instance (Metric c a, Metric c (Tuple as), Ord c, Floating c) => Metric c (NETup (a ':| as)) where
    NET x xs <.> NET y ys = (x <.> y) + (xs <.> ys)
    norm_inf (NET x xs)   = max (norm_inf x) (norm_inf xs)
    norm_0 (NET x xs)     = norm_0 x + norm_0 xs
    norm_1 (NET x xs)     = norm_1 x + norm_1 xs
    quadrance (NET x xs)  = quadrance x + quadrance xs

instance (Additive a, Additive (Tuple as), Ref m (NETup (a ':| as)) v)
        => AdditiveInPlace m v (NETup (a ':| as))
instance (Scaling s a, Scaling s (Tuple as), Ref m (NETup (a ':| as)) v)
        => ScalingInPlace m v s (NETup (a ':| as))

getTup :: ListC (Bi.Binary <$> as) => Length as -> Bi.Get (Tuple as)
getTup = \case
    LZ   -> pure Ø
    LS l -> do
      x  <- Bi.get
      xs <- getTup l
      pure (I x :< xs)

putTup :: ListC (Bi.Binary <$> as) => Tuple as -> Bi.Put
putTup = \case
    Ø -> pure ()
    I x :< xs -> Bi.put x *> putTup xs

instance (Bi.Binary a, ListC (Bi.Binary <$> as), Known Length as) => Bi.Binary (NETup (a ':| as)) where
    get = NET <$> Bi.get
              <*> getTup known
    put (NET x xs) = Bi.put x *> putTup xs

netHead :: Lens (NETup (a ':| as)) (NETup (b ':| as)) a b
netHead f (NET x xs) = (`NET` xs) <$> f x

netTail :: Lens (NETup (a ':| as)) (NETup (a ':| bs)) (Tuple as) (Tuple bs)
netTail f (NET x xs) = NET x <$> f xs

unNet :: NETup (a ':| as) -> (a, Tuple as)
unNet (NET x xs) = (x, xs)

type family ToNonEmpty (l :: [k]) = (m :: Maybe (NonEmpty k)) | m -> l where
    ToNonEmpty '[]       = 'Nothing
    ToNonEmpty (a ': as) = 'Just (a ':| as)

instance (Backprop a, ListC (Backprop <$> (I <$> as))) => Backprop (NETup (a ':| as)) where
    zero (NET x xs) = NET (zero x) (zero xs)
    add (NET x xs) (NET y ys) = NET (add x y) (add xs ys)
    one (NET x xs) = NET (one x) (one xs)
