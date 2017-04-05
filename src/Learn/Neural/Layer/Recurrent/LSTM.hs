{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PartialTypeSignatures     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE UndecidableInstances      #-}

module Learn.Neural.Layer.Recurrent.LSTM (
  ) where

import           Data.Kind
import           Data.Singletons.Prelude
import           GHC.Generics                   (Generic)
import           GHC.Generics.Numeric
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data LSTM :: Type

instance ( BLAS b
         , KnownNat i
         , KnownNat o
         , Floating (b '[o])
         , Floating (b '[o,i])
         , Floating (b '[o,o])
         )
        => Component LSTM b '[i] '[o] where

    data CParam LSTM b '[i] '[o] =
        LP { _lpForgetInp     :: !(b '[o,i])
           , _lpForgetState   :: !(b '[o,o])
           , _lpForgetBias    :: !(b '[o])
           , _lpRememberInp   :: !(b '[o,i])
           , _lpRememberState :: !(b '[o,o])
           , _lpRememberBias  :: !(b '[o])
           , _lpCommitInp     :: !(b '[o,i])
           , _lpCommitState   :: !(b '[o,o])
           , _lpCommitBias    :: !(b '[o])
           , _lpOutInp        :: !(b '[o,i])
           , _lpOutState      :: !(b '[o,o])
           , _lpOutBias       :: !(b '[o])
           }
      deriving (Generic)
    data CState LSTM b '[i] '[o] =
        LS { _lsCellState   :: !(b '[o])
           , _lsHiddenState :: !(b '[o])
           }
      deriving (Generic)
    type CConstr LSTM b '[i] '[o] = (Num (b '[o,i]), Num (b '[o,o]), Num (b '[o]))
    data CConf   LSTM b '[i] '[o] = forall d. ContGen d => LC d

    componentOp :: forall s. (Num (b '[i]), Num (b '[o]), CConstr LSTM b '[i] '[o])
        => OpB s '[b '[i], CParam LSTM b '[i] '[o], CState LSTM b '[i] '[o]] '[b '[o], CState LSTM b '[i] '[o]]
    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        fI :< fS :< fB :< rI :< rS :< rB :< cI :< cS :< cB :< oI :< oS :< oB :< Ø <- gTuple #<~ p
        sC :< sH :< Ø <- gTuple #<~ s
        let forget   = logistic $
                         sum [ matVecOp .$ (fI :< x  :< Ø)
                             , matVecOp .$ (fS :< sH :< Ø)
                             , fB
                             ]
            remember = logistic $
                         sum [ matVecOp .$ (rI :< x  :< Ø)
                             , matVecOp .$ (rS :< sH :< Ø)
                             , rB
                             ]
            commit   = tanh $
                         sum [ matVecOp .$ (cI :< x  :< Ø)
                             , matVecOp .$ (cS :< sH :< Ø)
                             , cB
                             ]
            out      = logistic $
                         sum [ matVecOp .$ (oI :< x  :< Ø)
                             , matVecOp .$ (oS :< sH :< Ø)
                             , oB
                             ]
        sC'      <- bindVar $ forget * sC + remember * commit
        finalOut <- bindVar $ out * tanh sC'
        s' :< Ø <- isoVar @s @_ @'[b '[o], b '[o]] @'[CState LSTM b '[i] '[o]]
                     (from gTuple . tup1)
                     (sC' :< finalOut :< Ø)
        return $ finalOut :< s' :< Ø
      where
        logistic :: Floating a => a -> a
        logistic x = 1 / (1 + exp (-x))

    defConf = LC (normalDistr 0 0.5)
    initParam = \case
      i `SCons` SNil -> \case
        so@(o `SCons` SNil) -> \(LC d) g -> do
          LP <$> genA (o `SCons` (i `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (o `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA so                           (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (i `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (o `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA so                           (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (i `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (o `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA so                           (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (i `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA (o `SCons` (o `SCons` SNil)) (\_ -> realToFrac <$> genContVar d g)
             <*> genA so                           (\_ -> realToFrac <$> genContVar d g)
        _ -> error "inaccessible"
      _ -> error "inaccessible"
    initState _ so (LC d) g =
        LS <$> genA so (\_ -> realToFrac <$> genContVar d g)
           <*> genA so (\_ -> realToFrac <$> genContVar d g)

instance ( BLAS b
         , KnownNat i
         , KnownNat o
         , Floating (b '[o])
         , Floating (b '[o,i])
         , Floating (b '[o,o])
         )
      => ComponentLayer 'Recurrent LSTM b '[i] '[o] where
    componentRunMode = RMNotFF

instance SOP.Generic (CState LSTM b '[i] '[o])
instance SOP.Generic (CParam LSTM b '[i] '[o])

instance (Num (b '[o,i]), Num (b '[o,o]), Num (b '[o])) => Num (CParam LSTM b '[i] '[o]) where
    (+)         = genericPlus
    (-)         = genericMinus
    (*)         = genericTimes
    negate      = genericNegate
    abs         = genericAbs
    signum      = genericSignum
    fromInteger = genericFromInteger

instance (Fractional (b '[o,i]), Fractional (b '[o,o]), Fractional (b '[o])) => Fractional (CParam LSTM b '[i] '[o]) where
    (/)          = genericDivide
    recip        = genericRecip
    fromRational = genericFromRational

instance (Floating (b '[o,i]), Floating (b '[o,o]), Floating (b '[o])) => Floating (CParam LSTM b '[i] '[o]) where
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

instance (Num (b '[o,i]), Num (b '[o,o]), Num (b '[o])) => Num (CState LSTM b '[i] '[o]) where
    (+)         = genericPlus
    (-)         = genericMinus
    (*)         = genericTimes
    negate      = genericNegate
    abs         = genericAbs
    signum      = genericSignum
    fromInteger = genericFromInteger

instance (Fractional (b '[o,i]), Fractional (b '[o,o]), Fractional (b '[o])) => Fractional (CState LSTM b '[i] '[o]) where
    (/)          = genericDivide
    recip        = genericRecip
    fromRational = genericFromRational

instance (Floating (b '[o,i]), Floating (b '[o,o]), Floating (b '[o])) => Floating (CState LSTM b '[i] '[o]) where
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

