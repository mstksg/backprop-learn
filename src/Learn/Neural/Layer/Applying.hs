{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}

module Learn.Neural.Layer.Applying (
    Applying
  , TensorOp(..)
  , CommonOp(..)
  , SoftMax
  ) where

import           Data.Kind
import           Data.Reflection
import           Data.Singletons
import           Learn.Neural.Layer
import           Numeric.BLASTensor
import           Numeric.Backprop

data Applying :: k -> Type

newtype TensorOp :: BShape -> BShape -> Type where
    TF :: { getTensorOp
                :: forall b s. (BLASTensor b, Num (b i), Num (b o)) => OpB s '[ b i ] '[ b o ]
          }
       -> TensorOp i o

instance Num (CParam (Applying s) b i o) where
    _ + _         = AppP
    _ * _         = AppP
    _ - _         = AppP
    negate _      = AppP
    abs    _      = AppP
    signum _      = AppP
    fromInteger _ = AppP

instance Fractional (CParam (Applying s) b i o) where
    _ / _          = AppP
    recip _        = AppP
    fromRational _ = AppP

instance Num (CState (Applying s) b i o) where
    _ + _         = AppS
    _ * _         = AppS
    _ - _         = AppS
    negate _      = AppS
    abs    _      = AppS
    signum _      = AppS
    fromInteger _ = AppS

instance Fractional (CState (Applying s) b i o) where
    _ / _          = AppS
    recip _        = AppS
    fromRational _ = AppS

instance (BLASTensor b, Reifies s (TensorOp i o), SingI i, SingI o) => Component (Applying s) b i o where
    data CParam (Applying s) b i o = AppP
    data CState (Applying s) b i o = AppS
    data CConf  (Applying s) b i o = AppC

    componentOp = componentOpDefault

    initParam _ _ _ _ = return AppP
    initState _ _ _ _ = return AppS
    defConf           = AppC

instance (BLASTensor b, Reifies s (TensorOp i o), SingI i, SingI o) => ComponentFF (Applying s) b i o where
    componentOpFF = bpOp . withInps $ \(x :< _ :< Ø) -> do
        y <- getTensorOp to ~$ (x :< Ø)
        return . only $ y
      where
        to :: TensorOp i o
        to = reflect (Proxy @s)

instance (BLASTensor b, Reifies s (TensorOp i o), SingI i, SingI o) => ComponentLayer r (Applying s) b i o where
    componentRunMode = RMIsFF

data CommonOp :: Type where
    TO_Softmax :: BShape -> CommonOp

instance SingI i => Reifies ('TO_Softmax i) (TensorOp i i) where
    reflect _ = TF $ bpOp . withInps $ \(x :< Ø) -> do
      expX <- tmapOp exp ~$ (x :< Ø)
      totX <- tsumOp     ~$ (expX   :< Ø)
      sm   <- scaleOp    ~$ (1/totX :< expX :< Ø)
      return $ only sm

type SoftMax i = Applying ('TO_Softmax i)
