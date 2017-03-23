{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Learn.Neural.Network (
    LChain(..)
  , Network(..)
  , networkOp
  , networkOpPure
  , NetConf(..)
  , initNet
  , NetStruct(..)
  , defNetConf
  , initDefNet
  ) where

import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Kind
import           Data.Singletons
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           System.Random.MWC


data LChain :: Type where
    (:~) :: BShape -> Type -> LChain

data Network :: RunMode -> (BShape -> Type) -> LChain -> [LChain] -> BShape -> Type where
    NetExt :: (Component c i o, CConstr c b i o)
           => Layer r c b i o
           -> Network r b (i ':~ c) '[] o
    (:&)   :: (Num (b h), Component c i h, Component d h o, CConstr c b i h, CConstr d b h o)
           => Layer r c b i h
           -> Network r b (h ':~ d) hs               o
           -> Network r b (i ':~ c) ((h ':~ d) ': hs) o

networkOp
    :: forall b i c hs o r s. (BLAS b, Tensor b, Num (b i), Num (b o))
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
    (l :: Layer r c b i h) :& (n2 :: Network r b (h ':~ d) js o) -> do
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
    :: forall b i c hs o s. (BLAS b, Tensor b, Num (b i), Num (b o))
    => OpB s '[ b i, Network 'FeedForward b (i ':~ c) hs o ] '[ b o ]
networkOpPure = OpM $ \(I x :< I n :< Ø) -> case n of
    NetExt l -> do
      (I y :< Ø, gF) <- runOpM' layerOpPure (x ::< l ::< Ø)
      let gF' = fmap (\case I dX :< I dL :< Ø -> dX ::< NetExt dL ::< Ø)
              . gF
      return (y ::< Ø, gF')
    (l :: Layer 'FeedForward c b i h) :& (n2 :: Network 'FeedForward b (h ':~ d) js o) -> do
      (I y :< Ø, gF ) <- runOpM' layerOpPure   (x ::< l ::< Ø)
      (I z :< Ø, gF') <- runOpM' networkOpPure (y ::< n2 ::< Ø)
      let gF'' :: Prod Maybe '[ b o ]
               -> ST s (Tuple '[ b i, Network 'FeedForward b (i ':~ c) ((h ':~ d) ': js) o])
          gF'' dZ = do
            I dY :< I dN2 :< Ø <- gF' dZ
            I dX :< I dL0 :< Ø <- gF  (Just dY :< Ø)
            return $ dX ::< (dL0 :& dN2) ::< Ø
      return (z ::< Ø, gF'')

data NetConf :: RunMode -> (BShape -> Type) -> LChain -> [LChain] -> BShape -> Type where
    NCExt :: (ComponentLayer r c i o, CConstr c b i o)
          => CConf c i o
          -> NetConf r b (i ':~ c) '[] o
    (:&~) :: (SingI h, Num (b h), ComponentLayer r c i h, ComponentLayer r d h o, CConstr c b i h, CConstr d b h o)
          => CConf c i h
          -> NetConf r b (h ':~ d) hs               o
          -> NetConf r b (i ':~ c) ((h ':~ d) ': hs) o

initNet
    :: forall b i c hs o m r. (PrimMonad m, BLAS b, Tensor b, SingI i, SingI o)
    => NetConf r b (i ':~ c) hs o
    -> Gen (PrimState m)
    -> m (Network r b (i ':~ c) hs o)
initNet = \case
    NCExt c -> \g -> NetExt <$> initLayer sing sing c g
    c :&~ cN -> \g -> do
      l <- initLayer sing sing c g
      n <- initNet cN g
      return $ l :& n

data NetStruct :: RunMode -> (BShape -> Type) -> LChain -> [LChain] -> BShape -> Type where
    NSExt :: ( ComponentLayer r c i o
             , CConstr c b i o
             )
          => NetStruct r b (i ':~ c) '[] o
    NSInt :: ( SingI h
             , Num (b h)
             , ComponentLayer r c i h
             , ComponentLayer r d h o
             , CConstr c b i h
             , CConstr d b h o
             )
          => NetStruct r b (h ':~ d) hs               o
          -> NetStruct r b (i ':~ c) ((h ':~ d) ': hs) o

defNetConf
    :: NetStruct r b i hs o
    -> NetConf r b i hs o
defNetConf = \case
    NSExt   -> NCExt defConf
    NSInt c -> defConf :&~ defNetConf c

initDefNet
    :: forall b i c hs o m r. (PrimMonad m, BLAS b, Tensor b, SingI i, SingI o)
    => NetStruct r b (i ':~ c) hs o
    -> Gen (PrimState m)
    -> m (Network r b (i ':~ c) hs o)
initDefNet = initNet . defNetConf
