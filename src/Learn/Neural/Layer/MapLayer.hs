{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

module Learn.Neural.Layer.MapLayer
  where


import           Data.Kind
import           Data.Proxy
import           Data.Reflection
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Data.Traversable
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Index
import           Data.Type.Length
import           Data.Type.Util
import           Data.Type.Vector
import           Learn.Neural
import           Numeric.AD
import           Numeric.AD.Internal.Reverse
import           Numeric.AD.Mode.Forward
import           Numeric.AD.Mode.Reverse
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           Statistics.Distribution
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import qualified Data.Type.Nat               as TCN
import qualified Type.Family.Nat             as TCN

data MapLayer :: k -> Type

data MapFunc :: Type where
    MF :: { runMapFunc :: (forall a. RealFloat a => a -> a)
          }
       -> MapFunc

instance Num (CParam (MapLayer s) b i i) where
    _ + _         = MapParams
    _ * _         = MapParams
    _ - _         = MapParams
    negate _      = MapParams
    abs    _      = MapParams
    signum _      = MapParams
    fromInteger _ = MapParams

instance (Reifies s MapFunc, SingI i) => Component (MapLayer s) i i where
    data CParam (MapLayer s) b i i = MapParams
    type CState (MapLayer s) b i i = 'Nothing

    componentOp = bpOp . withInps $ \(x :< _ :< Ø) -> do
        y <- tmapOp (runMapFunc mf) ~$ (x :< Ø)
        return $ only y
      where
        mf :: MapFunc
        mf = reflect (Proxy @s)

    initComponent _ _ _ = return $ only_ MapParams

data CommonMap :: Type where
    MFLogit :: CommonMap
    MFReLU  :: CommonMap
    MFReLUp :: a -> CommonMap
    MFELU   :: CommonMap
    MFELUp  :: a -> CommonMap

instance Reifies 'MFLogit MapFunc where
    reflect _ = MF $ \x -> 1 / (1 + exp (-x))
instance Reifies 'MFReLU MapFunc where
    reflect _ = MF $ \x -> if x < 0 then 0 else x
instance Reifies s Double => Reifies ('MFReLUp s) MapFunc where
    reflect _ = MF $ \x -> if x < 0 then realToFrac α * x else x
      where
        α :: Double
        α = reflect (Proxy @s)
instance Reifies 'MFELU MapFunc where
    reflect _ = MF $ \x -> if x < 0 then exp x - 1 else x
instance Reifies s Double => Reifies ('MFELUp s) MapFunc where
    reflect _ = MF $ \x -> if x < 0 then realToFrac α * exp x - 1 else x
      where
        α :: Double
        α = reflect (Proxy @s)

type Logit  = MapLayer 'MFLogit
type ReLU   = MapLayer 'MFReLU
type ReLUp  = MapLayer 'MFReLUp
type ELU    = MapLayer 'MFELU
type ELUp s = MapLayer ('MFELUp s)

data PMapLayer :: k -> TCN.N -> Type

data PMapFunc :: TCN.N -> Type where
    PMF :: { runPMapFunc  :: (forall a. RealFloat a => (I :&: Vec n) a -> a)
           , initPMapFunc :: Vec n (SomeC ContGen I)
           }
        -> PMapFunc n

instance Num (CParam (PMapLayer s n) b i i) where

pMapParams :: Iso' (CParam (PMapLayer s n) b i i) (Tuple (Replicate n (ElemT b)))
pMapParams = iso undefined undefined

instance (Reifies s (PMapFunc n), SingI i, Known TCN.Nat n) => Component (PMapLayer s n) i i where
    data CParam (PMapLayer s n) b i i = PMapParams { getPMapParams :: !(Vec n (ElemT b)) }
    type CState (PMapLayer s n) b i i = 'Nothing

    componentOp
        :: forall q b. (BLAS b, Tensor b, Num (b i))
        => OpB q '[b i, CParam (PMapLayer s n) b i i] '[b i]
    componentOp = bpOp . withInps $ \(x :< mp :< Ø) -> replWit @n @Num @(ElemT b) n Wit //
                                                       replLen @n @(ElemT b) n          // do
        ps :: Prod (BVar q '[b i, CParam (PMapLayer s n) b i i]) (Replicate n (ElemT b))
          <- replWit @n @Num @(ElemT b) n Wit //
             replLen @n @(ElemT b) n //
               (pMapParams #<~ mp)
        let psV :: VecT n (BVar q '[b i, CParam (PMapLayer s n) b i i]) (ElemT b)
            psV = prodToVec' n ps
        psTV :: VecT n (BVar q '[b i, CParam (PMapLayer s n) b i i]) (b i)
          <- vtraverse (\p -> tkonstOp sing ~$ (p :< Ø)) psV
        let psT :: Prod (BVar q '[b i, CParam (PMapLayer s n) b i i]) (Replicate n (b i))
            psT = vecToProd psTV
        y <- tzipNOp @_ @_ @_ @('TCN.S n) (\case x' :* psT' -> runPMapFunc pmf (x' :&: psT'))
               ~$ (x :< psT)
        return $ only y
      where
        n :: TCN.Nat n
        n = known
        pmf :: PMapFunc n
        pmf = reflect (Proxy @s)

    initComponent _ _ g = do
        ps <- forM (initPMapFunc pmf) $ \(SomeC (I d)) ->
          realToFrac <$> genContVar d g
        return $ only_ (PMapParams ps)
      where
        pmf :: PMapFunc n
        pmf = reflect (Proxy @s)
