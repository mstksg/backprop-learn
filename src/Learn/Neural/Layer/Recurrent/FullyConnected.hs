{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

module Learn.Neural.Layer.Recurrent.FullyConnected (
    FullyConnectedR
  , FullyConnectedR'
  , CommonMap(..)
  , MapFunc(..)
  ) where

import           Data.Kind
import           Data.Proxy
import           Data.Reflection
import           Data.Singletons.Prelude
import           GHC.Generics                   (Generic)
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Learn.Neural.Layer.Mapping
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso           (iso)
import           Numeric.Backprop.Op
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data FullyConnectedR :: Type

deriving instance Generic (CParam FullyConnectedR b '[i] '[o])
instance SOP.Generic (CParam FullyConnectedR b '[i] '[o])

instance (Num (b '[o,o]), Num (b '[o,i]), Num (b '[o]))
      => Num (CParam FullyConnectedR b '[i] '[o]) where
    FCRP wI1 wS1 b1 + FCRP wI2 wS2 b2 = FCRP (wI1 + wI2) (wS1 + wS2) (b1 + b2)
    FCRP wI1 wS1 b1 - FCRP wI2 wS2 b2 = FCRP (wI1 - wI2) (wS1 - wS2) (b1 - b2)
    FCRP wI1 wS1 b1 * FCRP wI2 wS2 b2 = FCRP (wI1 * wI2) (wS1 * wS2) (b1 * b2)
    negate (FCRP wI wS b) = FCRP (negate wI) (negate wS) (negate b)
    signum (FCRP wI wS b) = FCRP (signum wI) (signum wS) (signum b)
    abs    (FCRP wI wS b) = FCRP (abs    wI) (abs    wS) (abs    b)
    fromInteger x = FCRP (fromInteger x) (fromInteger x) (fromInteger x)

instance (Fractional (b '[o,o]), Fractional (b '[o,i]), Fractional (b '[o]))
      => Fractional (CParam FullyConnectedR b '[i] '[o]) where
    FCRP wI1 wS1 b1 / FCRP wI2 wS2 b2 = FCRP (wI1 / wI2) (wS1 / wS2) (b1 / b2)
    recip (FCRP wI wS b) = FCRP (recip wI) (recip wS) (recip b)
    fromRational x       = FCRP (fromRational x) (fromRational x) (fromRational x)

instance (Floating (b '[o,o]), Floating (b '[o,i]), Floating (b '[o]))
      => Floating (CParam FullyConnectedR b '[i] '[o]) where
    sqrt (FCRP wI wS b) = FCRP (sqrt wI) (sqrt wS) (sqrt b)

instance Num (b '[o]) => Num (CState FullyConnectedR b '[i] '[o]) where
    FCRS s1 + FCRS s2 = FCRS (s1 + s2)
    FCRS s1 - FCRS s2 = FCRS (s1 - s2)
    FCRS s1 * FCRS s2 = FCRS (s1 * s2)
    negate (FCRS s) = FCRS (negate s)
    signum (FCRS s) = FCRS (signum s)
    abs    (FCRS s) = FCRS (abs    s)
    fromInteger x  = FCRS (fromInteger x)

instance Fractional (b '[o]) => Fractional (CState FullyConnectedR b '[i] '[o]) where
    FCRS s1 / FCRS s2 = FCRS (s1 / s2)
    recip (FCRS s)    = FCRS (recip s)
    fromRational x    = FCRS (fromRational x)

instance Floating (b '[o]) => Floating (CState FullyConnectedR b '[i] '[o]) where
    sqrt (FCRS s)    = FCRS (sqrt s)

instance ( BLAS b
         , KnownNat i
         , KnownNat o
         , Floating (b '[o])
         , Floating (b '[o,i])
         , Floating (b '[o,o])
         )
        => Component FullyConnectedR b '[i] '[o] where
    data CParam  FullyConnectedR b '[i] '[o] =
            FCRP { _fcrInpWeights   :: !(b '[o,i])
                 , _fcrStateWeights :: !(b '[o,o])
                 , _fcrBiases       :: !(b '[o])
                 }
    data CState  FullyConnectedR b '[i] '[o] = FCRS { _fcrState :: !(b '[o]) }
    type CConstr FullyConnectedR b '[i] '[o] = (Num (b '[o,i]), Num (b '[o,o]))
    data CConf   FullyConnectedR b '[i] '[o] = forall d. ContGen d => FCRC d

    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        wI :< wS :< b :< Ø <- gTuple #<~ p
        s0 <- opIso (iso _fcrState FCRS) ~$ (s :< Ø)
        y  <- matVecOp ~$ (wI :< x  :< Ø)
        s1 <- matVecOp ~$ (wS :< s0 :< Ø)
        let z = y + s1 + b
        s' <- opIso (iso FCRS _fcrState) ~$ (s1 :< Ø)
        return $ z :< s' :< Ø

    defConf = FCRC (normalDistr 0 0.01)
    initParam = \case
      i `SCons` SNil -> \case
        so@(o `SCons` SNil) -> \(FCRC d) g -> do
          wI <- genA (o `SCons` (i `SCons` SNil)) $ \_ ->
            realToFrac <$> genContVar d g
          wS <- genA (o `SCons` (o `SCons` SNil)) $ \_ ->
            realToFrac <$> genContVar d g
          b <- genA so $ \_ ->
            realToFrac <$> genContVar d g
          return $ FCRP wI wS b
        _ -> error "inaccessible"
      _ -> error "inaccessible"
    initState _ so (FCRC d) g =
        FCRS <$> genA so (\_ -> realToFrac <$> genContVar d g)

instance ( BLAS b
         , KnownNat i
         , KnownNat o
         , Floating (b '[o])
         , Floating (b '[o,i])
         , Floating (b '[o,o])
         )
        => ComponentLayer 'Recurrent FullyConnectedR b '[i] '[o] where
    componentRunMode = RMNotFF

data FullyConnectedR' :: k -> Type

deriving instance Generic (CParam (FullyConnectedR' c) b '[i] '[o])
instance SOP.Generic (CParam (FullyConnectedR' c) b '[i] '[o])

instance (Num (b '[o,o]), Num (b '[o,i]), Num (b '[o]))
      => Num (CParam (FullyConnectedR' s) b '[i] '[o]) where
    FCRP' wI1 wS1 b1 + FCRP' wI2 wS2 b2 = FCRP' (wI1 + wI2) (wS1 + wS2) (b1 + b2)
    FCRP' wI1 wS1 b1 - FCRP' wI2 wS2 b2 = FCRP' (wI1 - wI2) (wS1 - wS2) (b1 - b2)
    FCRP' wI1 wS1 b1 * FCRP' wI2 wS2 b2 = FCRP' (wI1 * wI2) (wS1 * wS2) (b1 * b2)
    negate (FCRP' wI wS b) = FCRP' (negate wI) (negate wS) (negate b)
    signum (FCRP' wI wS b) = FCRP' (signum wI) (signum wS) (signum b)
    abs    (FCRP' wI wS b) = FCRP' (abs    wI) (abs    wS) (abs    b)
    fromInteger x = FCRP' (fromInteger x) (fromInteger x) (fromInteger x)

instance (Fractional (b '[o,o]), Fractional (b '[o,i]), Fractional (b '[o]))
      => Fractional (CParam (FullyConnectedR' s) b '[i] '[o]) where
    FCRP' wI1 wS1 b1 / FCRP' wI2 wS2 b2 = FCRP' (wI1 / wI2) (wS1 / wS2) (b1 / b2)
    recip (FCRP' wI wS b) = FCRP' (recip wI) (recip wS) (recip b)
    fromRational x        = FCRP' (fromRational x) (fromRational x) (fromRational x)

instance (Floating (b '[o,o]), Floating (b '[o,i]), Floating (b '[o]))
      => Floating (CParam (FullyConnectedR' s) b '[i] '[o]) where
    sqrt (FCRP' wI wS b) = FCRP' (sqrt wI) (sqrt wS) (sqrt b)

instance Num (b '[o]) => Num (CState (FullyConnectedR' s) b '[i] '[o]) where
    FCRS' s1 + FCRS' s2 = FCRS' (s1 + s2)
    FCRS' s1 - FCRS' s2 = FCRS' (s1 - s2)
    FCRS' s1 * FCRS' s2 = FCRS' (s1 * s2)
    negate (FCRS' s) = FCRS' (negate s)
    signum (FCRS' s) = FCRS' (signum s)
    abs    (FCRS' s) = FCRS' (abs    s)
    fromInteger x  = FCRS' (fromInteger x)

instance Fractional (b '[o]) => Fractional (CState (FullyConnectedR' s) b '[i] '[o]) where
    FCRS' s1 / FCRS' s2 = FCRS' (s1 / s2)
    recip (FCRS' s)     = FCRS' (recip s)
    fromRational x      = FCRS' (fromRational x)

instance Floating (b '[o]) => Floating (CState (FullyConnectedR' s) b '[i] '[o]) where
    sqrt (FCRS' s)     = FCRS' (sqrt s)


instance ( BLAS b
         , KnownNat i
         , KnownNat o
         , Floating (b '[o])
         , Floating (b '[o,i])
         , Floating (b '[o,o])
         , Reifies c MapFunc
         )
      => Component (FullyConnectedR' c) b '[i] '[o] where
    data CParam  (FullyConnectedR' c) b '[i] '[o] =
            FCRP' { _fcrInpWeights'   :: !(b '[o,i])
                  , _fcrStateWeights' :: !(b '[o,o])
                  , _fcrBiases'       :: !(b '[o])
                  }
    data CState  (FullyConnectedR' c) b '[i] '[o] = FCRS' { _fcrState' :: !(b '[o]) }
    type CConstr (FullyConnectedR' c) b '[i] '[o] =
      ( Num (b '[o,i])
      , Num (b '[o,o])
      )
    data CConf   (FullyConnectedR' c) b '[i] '[o] = forall d. ContGen d => FCRC' d

    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        wI :< wS :< b :< Ø <- gTuple #<~ p
        s0 <- opIso (iso _fcrState' FCRS') ~$ (s :< Ø)
        y  <- matVecOp ~$ (wI :< x  :< Ø)
        s1 <- matVecOp ~$ (wS :< s0 :< Ø)
        s2 <- tmapOp (runMapFunc mf) ~$ (s1 :< Ø)
        let z = y + s2 + b
        s' <- opIso (iso FCRS' _fcrState') ~$ (s2 :< Ø)
        return $ z :< s' :< Ø
      where
        mf :: MapFunc
        mf = reflect (Proxy @c)

    defConf = FCRC' (normalDistr 0 0.01)

    initParam = \case
      i `SCons` SNil -> \case
        so@(o `SCons` SNil) -> \(FCRC' d) g -> do
          wI <- genA (o `SCons` (i `SCons` SNil)) $ \_ ->
            realToFrac <$> genContVar d g
          wS <- genA (o `SCons` (o `SCons` SNil)) $ \_ ->
            realToFrac <$> genContVar d g
          b <- genA so $ \_ ->
            realToFrac <$> genContVar d g
          return $ FCRP' wI wS b
        _ -> error "inaccessible"
      _ -> error "inaccessible"

    initState _ so (FCRC' d) g =
        FCRS' <$> genA so (\_ -> realToFrac <$> genContVar d g)

instance ( BLAS b
         , KnownNat i
         , KnownNat o
         , Floating (b '[o])
         , Floating (b '[o,i])
         , Floating (b '[o,o])
         , Reifies s MapFunc
         )
      => ComponentLayer 'Recurrent (FullyConnectedR' s) b '[i] '[o] where
    componentRunMode = RMNotFF

