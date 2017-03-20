{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

module Learn.Neural.Layer.Map
  where


import           Data.Kind
import           Data.Proxy
import           Data.Reflection
import           Data.Singletons
import           Data.Traversable
import           Data.Type.Combinator
import           Data.Type.Conjunction
import           Data.Type.Util
import           Data.Type.Vector hiding         (head')
import           GHC.Generics                    (Generic)
import           Learn.Neural
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           Statistics.Distribution
import           Statistics.Distribution.Uniform
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import qualified Data.Type.Nat                   as TCN
import qualified Generics.SOP                    as SOP
import qualified Type.Family.Nat                 as TCN

data MapLayer :: k -> Type

data MapFunc :: Type where
    MF :: { runMapFunc :: (forall a. RealFloat a => a -> a)
          }
       -> MapFunc

instance Num (CParam (MapLayer s) b i i) where
    _ + _         = MapP
    _ * _         = MapP
    _ - _         = MapP
    negate _      = MapP
    abs    _      = MapP
    signum _      = MapP
    fromInteger _ = MapP

instance (Reifies s MapFunc, SingI i) => Component (MapLayer s) i i where
    data CParam (MapLayer s) b i i = MapP
    type CState (MapLayer s) b i i = 'Nothing

    componentOp = bpOp . withInps $ \(x :< _ :< Ø) -> do
        y <- tmapOp (runMapFunc mf) ~$ (x :< Ø)
        return $ only y
      where
        mf :: MapFunc
        mf = reflect (Proxy @s)

    initComponent _ _ _ = return $ only_ MapP

data CommonMap :: Type where
    MF_Logit :: CommonMap
    MF_ReLU  :: CommonMap
    MF_ReLUp :: a -> CommonMap
    MF_ELU   :: CommonMap
    MF_ELUp  :: a -> CommonMap

instance Reifies 'MF_Logit MapFunc where
    reflect _ = MF $ \x -> 1 / (1 + exp (-x))
instance Reifies 'MF_ReLU MapFunc where
    reflect _ = MF $ \x -> if x < 0 then 0 else x
instance Reifies s Double => Reifies ('MF_ReLUp s) MapFunc where
    reflect _ = MF $ \x -> if x < 0 then realToFrac α * x else x
      where
        α :: Double
        α = reflect (Proxy @s)
instance Reifies 'MF_ELU MapFunc where
    reflect _ = MF $ \x -> if x < 0 then exp x - 1 else x
instance Reifies s Double => Reifies ('MF_ELUp s) MapFunc where
    reflect _ = MF $ \x -> if x < 0 then realToFrac α * (exp x - 1) else x
      where
        α :: Double
        α = reflect (Proxy @s)

type Logit   = MapLayer 'MF_Logit
type ReLU    = MapLayer 'MF_ReLU
type ReLUp s = MapLayer ('MF_ReLUp s)
type ELU     = MapLayer 'MF_ELU
type ELUp s  = MapLayer ('MF_ELUp s)

data PMapLayer :: k -> TCN.N -> Type

data PMapFunc :: TCN.N -> Type where
    PMF :: { runPMapFunc  :: (forall a. RealFloat a => (I :&: Vec n) a -> a)
           , initPMapFunc :: Vec n (SomeC ContGen I)
           }
        -> PMapFunc n

instance (Tensor b, Known TCN.Nat n) => Num (CParam (PMapLayer s n) b i i) where
    PMapP x + PMapP y = PMapP $ x + y
    PMapP x - PMapP y = PMapP $ x - y
    PMapP x * PMapP y = PMapP $ x * y
    negate (PMapP x) = PMapP (negate x)
    abs    (PMapP x) = PMapP (abs    x)
    signum (PMapP x) = PMapP (signum x)
    fromInteger x         = PMapP (fromInteger x)

pMapP :: Known TCN.Nat n => Iso' (CParam (PMapLayer s n) b i i) (Tuple (Replicate n (ElemT b)))
pMapP = gTuple . iso (vecToProd . getI . head') (only_ . prodToVec' known)

deriving instance Generic (CParam (PMapLayer s n) b i i)
instance SOP.Generic (CParam (PMapLayer s n) b i i)

instance (Reifies s (PMapFunc n), SingI i, Known TCN.Nat n) => Component (PMapLayer s n) i i where
    data CParam (PMapLayer s n) b i i = PMapP { getPMapP :: !(Vec n (ElemT b)) }
    type CState (PMapLayer s n) b i i = 'Nothing

    componentOp
        :: forall q b. (BLAS b, Tensor b, Num (b i))
        => OpB q '[b i, CParam (PMapLayer s n) b i i] '[b i]
    componentOp = bpOp . withInps $ \(x :< mp :< Ø) -> replWit @n @Num @(ElemT b) n Wit //
                                                       replLen @n @(ElemT b) n          // do
        ps :: Prod (BVar q '[b i, CParam (PMapLayer s n) b i i]) (Replicate n (ElemT b))
          <- replWit @n @Num @(ElemT b) n Wit //
             replLen @n @(ElemT b) n //
               pMapP #<~ mp
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
        return $ only_ (PMapP ps)
      where
        pmf :: PMapFunc n
        pmf = reflect (Proxy @s)

data CommonPMap :: Type where
    PMF_PReLU :: CommonPMap
    PMF_PELU  :: CommonPMap

instance Reifies 'PMF_PReLU (PMapFunc TCN.N1) where
    reflect _ = PMF (\case I x :&: (I α :* ØV) ->
                            if x < 0 then α * x else x)
                    (SomeC (I (uniformDistr 0 1)) :+ ØV)

instance Reifies 'PMF_PELU (PMapFunc TCN.N1) where
    reflect _ = PMF (\case I x :&: (I α :* ØV) ->
                            if x < 0 then α * (exp x - 1) else x)
                    (SomeC (I (uniformDistr 0 1)) :+ ØV)

type PReLU = PMapLayer 'PMF_PReLU
type PELU  = PMapLayer 'PMF_PELU
