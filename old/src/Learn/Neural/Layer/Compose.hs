{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Learn.Neural.Layer.Compose (
  ) where

import           Data.Kind
import           Data.Singletons
import           GHC.Generics         (Generic)
import           GHC.Generics.Numeric
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso
import qualified Generics.SOP         as SOP

data Comp :: Type -> Type -> k -> Type

instance ( BLAS b
         , Component l b i h
         , Component j b h o
         )
      => Component (Comp l j h) b i o where
    data CParam (Comp l j h) b i o = CP { _cp1 :: !(CParam l b i h)
                                        , _cp2 :: !(CParam j b h o)
                                        }
      deriving Generic
    data CState (Comp l j h) b i o = CS { _cs1 :: !(CState l b i h)
                                        , _cs2 :: !(CState j b h o)
                                        }
      deriving Generic
    type CConstr (Comp l j h) b i o =
        ( CConstr l b i h
        , CConstr j b h o
        , Num (b h)
        , SingI h
        )
    data CConf (Comp l j h) b i o = CC { _cc1 :: !(CConf l b i h)
                                       , _cc2 :: !(CConf j b h o)
                                       }

    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        p1 :< p2  :< Ø <- cpIso #<~ p
        s1 :< s2  :< Ø <- csIso #<~ s
        y  :< s1' :< Ø <- componentOp ~$$ (x :< p1 :< s1 :< Ø)
        z  :< s2' :< Ø <- componentOp ~$$ (y :< p2 :< s2 :< Ø)
        s' :< Ø        <- isoVar (from csIso . tup1) (s1' :< s2' :< Ø)
        return $ z :< s' :< Ø

    initParam si so (CC c1 c2) g =
        CP <$> initParam si sh c1 g
           <*> initParam sh so c2 g
      where
        sh :: Sing h
        sh = sing

    initState si so (CC c1 c2) g =
        CS <$> initState si sh c1 g
           <*> initState sh so c2 g
      where
        sh :: Sing h
        sh = sing

    defConf = CC defConf defConf


cpIso :: Iso' (CParam (Comp l j h) b i o) (Tuple '[CParam l b i h, CParam j b h o])
cpIso = iso (\case CP c1 c2 -> c1 ::< c2 ::< Ø) (\case I c1 :< I c2 :< Ø -> CP c1 c2)

csIso :: Iso' (CState (Comp l j h) b i o) (Tuple '[CState l b i h, CState j b h o])
csIso = iso (\case CS s1 s2 -> s1 ::< s2 ::< Ø) (\case I s1 :< I s2 :< Ø -> CS s1 s2)

instance (SOP.Generic (CState l b i h), SOP.Generic (CState j b h o))
    => SOP.Generic (CState (Comp l j h) b i o)
instance (SOP.Generic (CParam l b i h), SOP.Generic (CParam j b h o))
    => SOP.Generic (CParam (Comp l j h) b i o)

instance (Num (CParam l b i h), Num (CParam j b h o))
      => Num (CParam (Comp l j h) b i o) where
    (+)         = genericPlus
    (-)         = genericMinus
    (*)         = genericTimes
    negate      = genericNegate
    abs         = genericAbs
    signum      = genericSignum
    fromInteger = genericFromInteger

instance (Fractional (CParam l b i h), Fractional (CParam j b h o))
      => Fractional (CParam (Comp l j h) b i o) where
    (/)          = genericDivide
    recip        = genericRecip
    fromRational = genericFromRational

instance (Floating (CParam l b i h), Floating (CParam j b h o))
      => Floating (CParam (Comp l j h) b i o) where
    pi      = genericPi
    exp     = genericExp
    (**)    = genericPower
    log     = genericLog
    logBase = genericLogBase
    sin     = genericSin
    cos     = genericCos
    tan     = genericTan
    asin    = genericAsin
    acos    = genericAcos
    atan    = genericAtan
    sinh    = genericSinh
    cosh    = genericCosh
    tanh    = genericTanh
    asinh   = genericAsinh
    acosh   = genericAcosh
    atanh   = genericAtanh

instance (Num (CState l b i h), Num (CState j b h o))
      => Num (CState (Comp l j h) b i o) where
    (+)         = genericPlus
    (-)         = genericMinus
    (*)         = genericTimes
    negate      = genericNegate
    abs         = genericAbs
    signum      = genericSignum
    fromInteger = genericFromInteger

instance (Fractional (CState l b i h), Fractional (CState j b h o))
      => Fractional (CState (Comp l j h) b i o) where
    (/)          = genericDivide
    recip        = genericRecip
    fromRational = genericFromRational

instance (Floating (CState l b i h), Floating (CState j b h o))
      => Floating (CState (Comp l j h) b i o) where
    pi      = genericPi
    exp     = genericExp
    (**)    = genericPower
    log     = genericLog
    logBase = genericLogBase
    sin     = genericSin
    cos     = genericCos
    tan     = genericTan
    asin    = genericAsin
    acos    = genericAcos
    atan    = genericAtan
    sinh    = genericSinh
    cosh    = genericCosh
    tanh    = genericTanh
    asinh   = genericAsinh
    acosh   = genericAcosh
    atanh   = genericAtanh
