{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}


module Learn.Neural.Layer.Identity (
    Ident
  ) where

import           Data.Kind
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop

data Ident :: Type

instance Num (CParam Ident b i i) where
    _ + _         = IdP
    _ * _         = IdP
    _ - _         = IdP
    negate _      = IdP
    abs    _      = IdP
    signum _      = IdP
    fromInteger _ = IdP

instance Fractional (CParam Ident b i i) where
    _ / _          = IdP
    recip _        = IdP
    fromRational _ = IdP

instance Floating (CParam Ident b i i) where
    sqrt _ = IdP

instance Num (CState Ident b i i) where
    _ + _         = IdS
    _ * _         = IdS
    _ - _         = IdS
    negate _      = IdS
    abs    _      = IdS
    signum _      = IdS
    fromInteger _ = IdS

instance Fractional (CState Ident b i i) where
    _ / _          = IdS
    recip _        = IdS
    fromRational _ = IdS

instance Floating (CState Ident b i i) where
    sqrt _ = IdS

instance BLAS b => Component Ident b i i where
    data CParam Ident b i i = IdP
    data CState Ident b i i = IdS
    data CConf  Ident b i i = IdC

    componentOp = componentOpDefault

    initParam _ _ _ _ = return IdP
    initState _ _ _ _ = return IdS
    defConf           = IdC

instance BLAS b => ComponentFF Ident b i i where
    componentOpFF = bpOp . withInps $ \(x :< _ :< Ø) ->
      return . only $ x

instance BLAS b => ComponentLayer r Ident b i i where
    componentRunMode = RMIsFF
