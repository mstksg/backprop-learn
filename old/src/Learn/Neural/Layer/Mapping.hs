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

module Learn.Neural.Layer.Mapping (
    Mapping
  , CommonMap(..)
  , IdentMap, ScaleMap, LogitMap, ReLUMap, ReLUpMap, ELUMap, ELUpMap
  , MapFunc(..)
  , PMapping
  , CommonPMap(..)
  , PReLUMap, PELUMap
  , PMapFunc(..)
  ) where


import           Control.Applicative
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
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso
import           Numeric.Backprop.Op
import           Statistics.Distribution
import           Statistics.Distribution.Uniform
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import qualified Data.Type.Nat                   as TCN
import qualified Generics.SOP                    as SOP
import qualified Type.Family.Nat                 as TCN

data Mapping :: k -> Type

newtype MapFunc :: Type where
    MF :: { runMapFunc :: (forall a. RealFloat a => a -> a)
          }
       -> MapFunc

instance Num (CParam (Mapping s) b i i) where
    _ + _         = MapP
    _ * _         = MapP
    _ - _         = MapP
    negate _      = MapP
    abs    _      = MapP
    signum _      = MapP
    fromInteger _ = MapP

instance Fractional (CParam (Mapping s) b i i) where
    _ / _          = MapP
    recip _        = MapP
    fromRational _ = MapP

instance Floating (CParam (Mapping s) b i i) where
    sqrt _ = MapP

instance Num (CState (Mapping s) b i i) where
    _ + _         = MapS
    _ * _         = MapS
    _ - _         = MapS
    negate _      = MapS
    abs    _      = MapS
    signum _      = MapS
    fromInteger _ = MapS

instance Fractional (CState (Mapping s) b i i) where
    _ / _          = MapS
    recip _        = MapS
    fromRational _ = MapS

instance Floating (CState (Mapping s) b i i) where
    sqrt _ = MapS

instance (BLAS b, Reifies s MapFunc, SingI i) => Component (Mapping s) b i i where
    data CParam (Mapping s) b i i = MapP
    data CState (Mapping s) b i i = MapS
    data CConf  (Mapping s) b i i = MapC

    componentOp = componentOpDefault

    initParam _ _ _ _ = return MapP
    initState _ _ _ _ = return MapS
    defConf           = MapC

instance (BLAS b, Reifies s MapFunc, SingI i) => ComponentFF (Mapping s) b i i where
    componentOpFF = bpOp . withInps $ \(x :< _ :< Ø) -> do
        y <- tmapOp (runMapFunc mf) ~$ (x :< Ø)
        return . only $ y
      where
        mf :: MapFunc
        mf = reflect (Proxy @s)

instance (BLAS b, Reifies s MapFunc, SingI i) => ComponentLayer r (Mapping s) b i i where
    componentRunMode = RMIsFF

data CommonMap :: Type where
    MF_Ident :: CommonMap
    MF_Scale :: a -> CommonMap
    MF_Logit :: CommonMap
    MF_Tanh  :: CommonMap
    MF_ReLU  :: CommonMap
    MF_ReLUp :: a -> CommonMap
    MF_ELU   :: CommonMap
    MF_ELUp  :: a -> CommonMap

instance Reifies 'MF_Ident MapFunc where
    reflect _ = MF id
instance Reifies s Double => Reifies ('MF_Scale s) MapFunc where
    reflect _ = MF $ (realToFrac α *)
      where
        α :: Double
        α = reflect (Proxy @s)
instance Reifies 'MF_Logit MapFunc where
    reflect _ = MF $ \x -> 1 / (1 + exp (-x))
instance Reifies 'MF_Tanh MapFunc where
    reflect _ = MF tanh
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

type IdentMap   = Mapping 'MF_Ident
type ScaleMap s = Mapping ('MF_Scale s)
type LogitMap   = Mapping 'MF_Logit
type TanhMap    = Mapping 'MF_Tanh
type ReLUMap    = Mapping 'MF_ReLU
type ReLUpMap s = Mapping ('MF_ReLUp s)
type ELUMap     = Mapping 'MF_ELU
type ELUpMap s  = Mapping ('MF_ELUp s)

data PMapping :: k -> TCN.N -> Type

data PMapFunc :: TCN.N -> Type where
    PMF :: { runPMapFunc :: (forall a. RealFloat a => (I :&: Vec n) a -> a)
           , getPMapDef  :: Vec n (SomeC ContGen I)
           }
        -> PMapFunc n

instance (Tensor b, Known TCN.Nat n) => Num (CParam (PMapping s n) b i i) where
    PMapP x + PMapP y = PMapP $ x + y
    PMapP x - PMapP y = PMapP $ x - y
    PMapP x * PMapP y = PMapP $ x * y
    negate (PMapP x) = PMapP (negate x)
    abs    (PMapP x) = PMapP (abs    x)
    signum (PMapP x) = PMapP (signum x)
    fromInteger x         = PMapP (fromInteger x)

-- until Vec has a Fractional instance
instance (Tensor b, Known TCN.Nat n) => Fractional (CParam (PMapping s n) b i i) where
    PMapP x / PMapP y = PMapP $ liftA2 (/) x y
    recip (PMapP x)   = PMapP $ fmap recip x
    fromRational x    = PMapP $ pure (fromRational x)

instance (Tensor b, Known TCN.Nat n) => Floating (CParam (PMapping s n) b i i) where
    sqrt (PMapP x)   = PMapP $ fmap sqrt x

instance Num (CState (PMapping s n) b i i) where
    _ + _         = PMapS
    _ * _         = PMapS
    _ - _         = PMapS
    negate _      = PMapS
    abs    _      = PMapS
    signum _      = PMapS
    fromInteger _ = PMapS

instance Fractional (CState (PMapping s n) b i i) where
    _ / _          = PMapS
    recip _        = PMapS
    fromRational _ = PMapS

instance Floating (CState (PMapping s n) b i i) where
    sqrt _        = PMapS

pMapP :: Known TCN.Nat n => Iso' (CParam (PMapping s n) b i i) (Tuple (Replicate n (Scalar b)))
pMapP = gTuple . iso (vecToProd . getI . head') (only_ . prodToVec' known)

deriving instance Generic (CParam (PMapping s n) b i i)
instance SOP.Generic (CParam (PMapping s n) b i i)

instance (BLAS b, Reifies s (PMapFunc n), SingI i, Known TCN.Nat n) => Component (PMapping s n) b i i where
    data CParam (PMapping s n) b i i = PMapP { _getPMapP :: !(Vec n (Scalar b)) }
    data CState (PMapping s n) b i i = PMapS
    data CConf  (PMapping s n) b i i = PMapC { _getPMapC :: !(Vec n (SomeC ContGen I)) }

    componentOp = componentOpDefault

    initParam _ _ c g = do
        ps <- forM (_getPMapC c) $ \(SomeC (I d)) ->
          realToFrac <$> genContVar d g
        return $ PMapP ps
    initState _ _ _ _ = return PMapS

    defConf = PMapC (getPMapDef pmf)
      where
        pmf :: PMapFunc n
        pmf = reflect (Proxy @s)

instance (BLAS b, Reifies s (PMapFunc n), SingI i, Known TCN.Nat n) => ComponentFF (PMapping s n) b i i where
    componentOpFF
        :: forall q. Num (b i)
        => OpB q '[b i, CParam (PMapping s n) b i i] '[b i]
    componentOpFF = bpOp . withInps $ \(x :< mp :< Ø) -> replWit @n @Num @(Scalar b) n Wit //
                                                         replLen @n @(Scalar b) n          // do
        ps :: Prod (BVar q '[b i, CParam (PMapping s n) b i i]) (Replicate n (Scalar b))
          <- replWit @n @Num @(Scalar b) n Wit //
             replLen @n @(Scalar b) n //
               pMapP #<~ mp
        let psV :: VecT n (BVar q '[b i, CParam (PMapping s n) b i i]) (Scalar b)
            psV = prodToVec' n ps
        psTV :: VecT n (BVar q '[b i, CParam (PMapping s n) b i i]) (b i)
          <- vtraverse (\p -> tkonstOp sing ~$ (p :< Ø)) psV
        let psT :: Prod (BVar q '[b i, CParam (PMapping s n) b i i]) (Replicate n (b i))
            psT = vecToProd psTV
        y <- tzipNOp @_ @_ @('TCN.S n) (\case x' :* psT' -> runPMapFunc pmf (x' :&: psT'))
               ~$ (x :< psT)
        return $ only y
      where
        n :: TCN.Nat n
        n = known
        pmf :: PMapFunc n
        pmf = reflect (Proxy @s)

instance (BLAS b, Reifies s (PMapFunc n), SingI i, Known TCN.Nat n) => ComponentLayer r (PMapping s n) b i i where
    componentRunMode = RMIsFF

data CommonPMap :: Type where
    PMF_PReLU :: CommonPMap
    PMF_PELU  :: CommonPMap

instance Reifies 'PMF_PReLU (PMapFunc TCN.N1) where
    reflect _ = PMF (\case I x :&: (I α :* ØV) ->
                            if x < 0 then α * x else x)
                    (SomeC (I (uniformDistr 0 0.01)) :+ ØV)

instance Reifies 'PMF_PELU (PMapFunc TCN.N1) where
    reflect _ = PMF (\case I x :&: (I α :* ØV) ->
                            if x < 0 then α * (exp x - 1) else x)
                    (SomeC (I (uniformDistr 0 0.01)) :+ ØV)

type PReLUMap = PMapping 'PMF_PReLU
type PELUMap  = PMapping 'PMF_PELU
