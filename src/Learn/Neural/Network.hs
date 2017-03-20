{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

module Learn.Neural.Network (
    LChain(..)
  , Network(..)
  , networkOp
  , networkOpPure
  , NetConf(..)
  , initNet
  , NetStruct(..)
  , defNetConf(..)
  ) where

import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Kind
import           Data.Singletons
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           System.Random.MWC


data LChain :: Type where
    (:~) :: BShape Nat -> Type -> LChain

data Network :: HasState -> (BShape Nat -> Type) -> LChain -> [LChain] -> BShape Nat -> Type where
    NetExt :: (Component c i o, CConstr c b i o)
           => Layer c r b i o
           -> Network r b (i ':~ c) '[] o
    (:&)   :: (Num (b h), Component c i h, Component d h o, CConstr c b i h, CConstr d b h o)
           => Layer c r b i h
           -> Network r b (h ':~ d) hs               o
           -> Network r b (i ':~ c) ((h ':~ d) ': hs) o

networkOp
    :: forall s r b i c hs o. (BLAS b, Tensor b, Num (b i), Num (b o))
    => OpB s '[ b i, Network r b (i ':~ c) hs o ] '[ b o, Network r b (i ':~ c) hs o ]
networkOp = OpM $ \(I x :< I n :< Ø) -> case n of
    NetExt l -> do
      (I y :< I l' :< Ø, gF) <- runOpM' layerOp (x ::< l ::< Ø)
      let gF' = fmap (\case I dX :< I dL :< Ø -> dX ::< NetExt dL ::< Ø)
              . gF
              . (\case dY :< Just (NetExt dL) :< Ø -> dY :< Just dL :< Ø
                       dY :< Nothing          :< Ø -> dY :< Nothing :< Ø
                )
      return (y ::< NetExt l' ::< Ø, gF')
    (l :: Layer c r b i h) :& (n2 :: Network r b (h ':~ d) js o) -> do
      (I y :< I l'  :< Ø, gF ) <- runOpM' layerOp   (x ::< l ::< Ø)
      (I z :< I n2' :< Ø, gF') <- runOpM' networkOp (y ::< n2 ::< Ø)
      let gF'' :: Prod Maybe '[ b o, Network r b (i ':~ c) ((h ':~ d) ': js) o]
               -> ST s (Tuple '[ b i, Network r b (i ':~ c) ((h ':~ d) ': js) o])
          gF'' = \case dZ :< Just (dL :& dN) :< Ø -> do
                         I dY :< I dN2 :< Ø <- gF' (dZ :< Just dN :< Ø)
                         I dX :< I dL0 :< Ø <- gF  (Just dY :< Just dL :< Ø)
                         return $ dX ::< (dL0 :& dN2) ::< Ø
                       dZ :< Nothing   :< Ø -> do
                         I dY :< I dN2 :< Ø <- gF' (dZ :< Nothing :< Ø)
                         I dX :< I dL0 :< Ø <- gF  (Just dY :< Nothing :< Ø)
                         return $ dX ::< (dL0 :& dN2) ::< Ø
      return (z ::< (l' :& n2') ::< Ø, gF'')

networkOpPure
    :: forall s b i c hs o. (BLAS b, Tensor b, Num (b i), Num (b o))
    => OpB s '[ b i, Network 'NoState b (i ':~ c) hs o ] '[ b o ]
networkOpPure = OpM $ \(I x :< I n :< Ø) -> case n of
    NetExt l -> do
      (I y :< Ø, gF) <- runOpM' layerOpPure (x ::< l ::< Ø)
      let gF' = fmap (\case I dX :< I dL :< Ø -> dX ::< NetExt dL ::< Ø)
              . gF
      return (y ::< Ø, gF')
    (l :: Layer c 'NoState b i h) :& (n2 :: Network 'NoState b (h ':~ d) js o) -> do
      (I y :< Ø, gF ) <- runOpM' layerOpPure   (x ::< l ::< Ø)
      (I z :< Ø, gF') <- runOpM' networkOpPure (y ::< n2 ::< Ø)
      let gF'' :: Prod Maybe '[ b o ]
               -> ST s (Tuple '[ b i, Network 'NoState b (i ':~ c) ((h ':~ d) ': js) o])
          gF'' dZ = do
            I dY :< I dN2 :< Ø <- gF' dZ
            I dX :< I dL0 :< Ø <- gF  (Just dY :< Ø)
            return $ dX ::< (dL0 :& dN2) ::< Ø
      return (z ::< Ø, gF'')

data NetConf :: HasState -> (BShape Nat -> Type) -> LChain -> [LChain] -> BShape Nat -> Type where
    NCExt :: (Component c i o, CConstr c b i o)
          => LayerConf c r b i o
          -> NetConf r b (i ':~ c) '[] o
    (:&~) :: (SingI h, Num (b h), Component c i h, Component d h o, CConstr c b i h, CConstr d b h o)
          => LayerConf c r b i h
          -> NetConf r b (h ':~ d) hs               o
          -> NetConf r b (i ':~ c) ((h ':~ d) ': hs) o
initNet
    :: forall r b i c hs o m. (PrimMonad m, BLAS b, Tensor b, SingI i, SingI o)
    => NetConf r b (i ':~ c) hs o
    -> Gen (PrimState m)
    -> m (Network r b (i ':~ c) hs o)
initNet = \case
    NCExt c -> \g -> NetExt <$> initLayer sing sing c g
    c :&~ cN -> \g -> do
      l <- initLayer sing sing c g
      n <- initNet cN g
      return $ l :& n

data NetStruct :: HasState -> (BShape Nat -> Type) -> LChain -> [LChain] -> BShape Nat -> Type where
    NSExt :: ( Component c i o
             , CConstr c b i o
             , DefLayerConf c r b i o
             )
          => NetStruct r b (i ':~ c) '[] o
    NSInt :: ( SingI h
             , Num (b h)
             , Component c i h
             , Component d h o
             , CConstr c b i h
             , CConstr d b h o
             , DefLayerConf c r b i h
             )
          => NetStruct r b (h ':~ d) hs               o
          -> NetStruct r b (i ':~ c) ((h ':~ d) ': hs) o

defNetConf
    :: NetStruct r b i hs o
    -> NetConf r b i hs o
defNetConf = \case
    NSExt   -> NCExt defLayerConf
    NSInt c -> defLayerConf :&~ defNetConf c
