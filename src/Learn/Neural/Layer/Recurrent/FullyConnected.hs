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
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeInType                #-}
{-# LANGUAGE TypeSynonymInstances      #-}
{-# LANGUAGE UndecidableInstances      #-}

module Learn.Neural.Layer.Recurrent.FullyConnected (
    FullyConnectedR
  ) where

import           Data.Kind
import           Data.Reflection
import           GHC.Generics                   (Generic)
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Learn.Neural.Layer.Mapping
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso           (iso)
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import qualified Generics.SOP                   as SOP

data FullyConnectedR :: Type

deriving instance Generic (CParam FullyConnectedR b (BV i) (BV o))
instance SOP.Generic (CParam FullyConnectedR b (BV i) (BV o))

instance Num (CParam FullyConnectedR b (BV i) (BV o))
instance Num (CState FullyConnectedR b (BV i) (BV o))

instance (KnownNat i, KnownNat o) => Component FullyConnectedR (BV i) (BV o) where
    data CParam  FullyConnectedR b (BV i) (BV o) =
            FCRP { fcrInpWeights   :: !(b (BM o i))
                 , fcrStateWeights :: !(b (BM o o))
                 , fcrBiases       :: !(b (BV o))
                 }
    data CState  FullyConnectedR b (BV i) (BV o) = FCRS { fcrState :: !(b (BV o)) }
    type CConstr FullyConnectedR b (BV i) (BV o) = (Num (b (BM o i)), Num (b (BM o o)))
    data CConf   FullyConnectedR   (BV i) (BV o) = forall d. ContGen d => FCRC d

    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        wI :< wS :< b :< Ø <- gTuple #<~ p
        s0 <- opIso (iso fcrState FCRS) ~$ (s :< Ø)
        y  <- matVecOp ~$ (wI :< x  :< Ø)
        s1 <- matVecOp ~$ (wS :< s0 :< Ø)
        z  <- bindVar $ y + s1 + b
        s' <- opIso (iso FCRS fcrState) ~$ (s1 :< Ø)
        return $ z :< s' :< Ø

    defConf = FCRC (normalDistr 0 0.5)
    initParam (SBV i) so@(SBV o) (FCRC d) g = do
        wI <- genA (SBM o i) $ \_ ->
          realToFrac <$> genContVar d g
        wS <- genA (SBM o o) $ \_ ->
          realToFrac <$> genContVar d g
        b <- genA so $ \_ ->
          realToFrac <$> genContVar d g
        return $ FCRP wI wS b
    initState _ so (FCRC d) g =
        FCRS <$> genA so (\_ -> realToFrac <$> genContVar d g)

instance (KnownNat i, KnownNat o) => ComponentLayer 'Recurrent FullyConnectedR (BV i) (BV o) where
    componentRunMode = RMNotFF

data FullyConnectedR' :: Type -> Type

deriving instance Generic (CParam (FullyConnectedR' c) b (BV i) (BV o))
instance SOP.Generic (CParam (FullyConnectedR' c) b (BV i) (BV o))

instance Num (CParam (FullyConnectedR' c) b (BV i) (BV o))
instance Num (CState (FullyConnectedR' c) b (BV i) (BV o))


instance (KnownNat i, KnownNat o, ComponentFF c (BV o) (BV o))
      => Component (FullyConnectedR' c) (BV i) (BV o) where
    data CParam  (FullyConnectedR' c) b (BV i) (BV o) =
            FCRP' { fcrInpWeights'   :: !(b (BM o i))
                  , fcrStateWeights' :: !(b (BM o o))
                  , fcrBiases'       :: !(b (BV o))
                  , fcrInternal'     :: !(CParam c b (BV o) (BV o))
                  }
    data CState  (FullyConnectedR' c) b (BV i) (BV o) = FCRS' { fcrState' :: !(b (BV o)) }
    type CConstr (FullyConnectedR' c) b (BV i) (BV o) =
      ( Num (b (BM o i))
      , Num (b (BM o o))
      , CConstr c b (BV o) (BV o)
      , Num (CParam c b (BV o) (BV o))
      )
    data CConf   (FullyConnectedR' c)   (BV i) (BV o) where
        FCRC' :: ContGen d
              => { fcrConf'    :: d 
                 , fcrConfInt' :: CConf c (BV o) (BV o)
                 }
              -> CConf (FullyConnectedR' c) (BV i) (BV o)

    componentOp = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
        wI :< wS :< b :< pI :< Ø <- gTuple #<~ p
        s0 <- opIso (iso fcrState' FCRS') ~$ (s :< Ø)
        y  <- matVecOp ~$ (wI :< x  :< Ø)
        s1 <- matVecOp ~$ (wS :< s0 :< Ø)
        z  <- bindVar $ y + s1 + b
        s2 <- componentOpFF ~$ (s1 :< pI :< Ø)
        s' <- opIso (iso FCRS' fcrState') ~$ (s2 :< Ø)
        return $ z :< s' :< Ø

    defConf = FCRC' (normalDistr 0 0.5) defConf

    initParam (SBV i) so@(SBV o) (FCRC' d c) g = do
        wI <- genA (SBM o i) $ \_ ->
          realToFrac <$> genContVar d g
        wS <- genA (SBM o o) $ \_ ->
          realToFrac <$> genContVar d g
        b <- genA so $ \_ ->
          realToFrac <$> genContVar d g
        p <- initParam so so c g
        return $ FCRP' wI wS b p

    initState _ so (FCRC' d _) g =
        FCRS' <$> genA so (\_ -> realToFrac <$> genContVar d g)

instance (KnownNat i, KnownNat o, ComponentFF c (BV o) (BV o))
      => ComponentLayer 'Recurrent (FullyConnectedR' c) (BV i) (BV o) where
    componentRunMode = RMNotFF

