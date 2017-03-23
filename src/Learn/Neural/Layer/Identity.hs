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
instance Num (CState Ident b i i) where
    _ + _         = IdS
    _ * _         = IdS
    _ - _         = IdS
    negate _      = IdS
    abs    _      = IdS
    signum _      = IdS
    fromInteger _ = IdS

instance Component Ident i i where
    data CParam Ident b i i = IdP
    data CState Ident b i i = IdS
    data CConf  Ident   i i = IdC

    componentOp = componentOpDefault

    initParam _ _ _ _ = return IdP
    initState _ _ _ _ = return IdS
    defConf           = IdC

instance ComponentFF Ident i i where
    componentOpFF = bpOp . withInps $ \(x :< _ :< Ø) ->
      return . only $ x

instance ComponentLayer r Ident i i where
    componentRunMode = RMIsFF
