{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE Strict                #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Learn.Neural.Network (
    LChain(..)
  , (:~)
  , Network(..)
  , networkOp
  , networkOpPure
  , networkOpRecurrent
  , networkOpRecurrent'
  , runNetwork
  , runNetworkPure
  , runNetworkRecurrent
  , runNetworkRecurrent'
  , runNetworkFeedback
  , runNetworkFeedbackForever
  , NetConf(..)
  , initNet
  , NetStruct(..)
  , defNetConf'
  , defNetConf
  , initDefNet'
  , initDefNet
  , SomeNet(..)
  , someNet
  ) where

import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Kind
import           Data.Singletons
import           Data.Type.Util
import           Data.Type.Vector
import           Learn.Neural.Layer
import           Numeric.BLASTensor
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           System.Random.MWC
import           Type.Class.Known
import           Type.Class.Witness
import qualified Data.List.NonEmpty      as NE
import qualified Data.Type.Nat           as TCN


data LChain :: Type where
    (:~) :: BShape -> Type -> LChain

type s :~ c = s ':~ c

data Network :: RunMode -> (BShape -> Type) -> LChain -> [LChain] -> BShape -> Type where
    NetExt :: (ComponentLayer r c b i o, CConstr c b i o)
           => Layer r c b i o
           -> Network r b (i :~ c) '[] o
    (:&)   :: (ComponentLayer r c b i h, CConstr c b i h, Num (b h))
           => Layer r c b i h
           -> Network r b (h :~ d) hs               o
           -> Network r b (i :~ c) ((h :~ d) ': hs) o

networkOp
    :: forall b i c hs o r s. (BLASTensor b, Num (b i), Num (b o))
    => OpB s '[ b i, Network r b (i :~ c) hs o ] '[ b o, Network r b (i :~ c) hs o ]
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
    :: forall b i c hs o s. (BLASTensor b, Num (b i), Num (b o))
    => OpB s '[ b i, Network 'FeedForward b (i :~ c) hs o ] '[ b o ]
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

networkOpRecurrent
    :: forall n b i c hs o s.
     ( Known (NetStruct 'Recurrent b (i :~ c) hs) o
     , BLASTensor b
     , Num (b o)
     , Num (b i)
     )
    => TCN.Nat n
    -> OpB s (Network 'Recurrent b (i :~ c) hs o ': Replicate n (b i))
             (Network 'Recurrent b (i :~ c) hs o ': Replicate n (b o))
networkOpRecurrent = \case
    TCN.Z_   -> idOp
    TCN.S_ n -> (replWit @_ @Num @(b i) n Wit //) $
                (replWit @_ @Num @(b o) n Wit //) $
                (replLen @_ @(b i) n          //) $
      bpOp . withInps $ \(n0 :< x :< xs) -> do
        y  :< n1 :< Ø <- networkOp ~$$ (x :< n0 :< Ø)
        n2 :< ys      <- networkOpRecurrent n ~$$ (n1 :< xs)
        return (n2 :< y :< ys)

networkOpRecurrent'
    :: forall n b i c hs o s.
     ( Known (NetStruct 'Recurrent b (i :~ c) hs) o
     , BLASTensor b
     , Num (b o)
     , Num (b i)
     )
    => TCN.Nat n
    -> OpB s (Network 'Recurrent b (i :~ c) hs o ': b i ': Replicate n (b i))
             '[Network 'Recurrent b (i :~ c) hs o, b o ]
networkOpRecurrent' = \case
    TCN.Z_   -> bpOp . withInps $ \(n0 :< x :< Ø) -> do
      y :< n1 :< Ø <- networkOp ~$$ (x :< n0 :< Ø)
      return (n1 :< y :< Ø)
    TCN.S_ n -> (replWit @_ @Num @(b i) n Wit //) $
                (replLen @_ @(b i) n          //) $
      bpOp . withInps $ \(n0 :< x :< xs) -> do
        _  :< n1 :< Ø <- networkOp ~$$ (x :< n0 :< Ø)
        n2 :< y  :< Ø <- networkOpRecurrent' n ~$$ (n1 :< xs)
        return (n2 :< y :< Ø)

runNetwork
    :: (Num (b i), Num (b o), BLASTensor b)
    => Network r b (i :~ c) hs o
    -> b i
    -> (b o, Network r b (i :~ c) hs o)
runNetwork n x = case runOpB networkOp (x ::< n ::< Ø) of
    I y :< I n' :< Ø -> (y, n')

runNetworkPure
    :: (Num (b i), Num (b o), BLASTensor b)
    => Network 'FeedForward b (i :~ c) hs o
    -> b i
    -> b o
runNetworkPure n x = case runOpB networkOpPure (x ::< n ::< Ø) of
    I y :< Ø -> y

runNetworkRecurrent
    :: (Num (b i), Num (b o), BLASTensor b)
    => Network 'Recurrent b (i :~ c) hs o
    -> [b i]
    -> ([b o], Network 'Recurrent b (i :~ c) hs o)
runNetworkRecurrent n0 = \case
    []   -> ([], n0)
    x:xs -> let (y , n1) = runNetwork n0 x
                (ys, n2) = runNetworkRecurrent n1 xs
            in  (y:ys, n2)

runNetworkRecurrent'
    :: (Num (b i), Num (b o), BLASTensor b)
    => Network 'Recurrent b (i :~ c) hs o
    -> NE.NonEmpty (b i)
    -> (b o, Network 'Recurrent b (i :~ c) hs o)
runNetworkRecurrent' n0 (x NE.:| xs) = case xs of
    y:ys -> runNetworkRecurrent' n1 (y NE.:| ys)
    []   -> (z, n1)
  where
    (z, n1) = runNetwork n0 x

runNetworkFeedback
    :: (Num (b i), Num (b o), BLASTensor b)
    => TCN.Nat n
    -> (b o -> b i)
    -> Network 'Recurrent b (i :~ c) hs o
    -> b i
    -> (VecT n b o, Network 'Recurrent b (i :~ c) hs o)
runNetworkFeedback = \case
    TCN.Z_   -> \_ n0 _ ->
      (ØV, n0)
    TCN.S_ n -> \f n0 x ->
      let (y , n1) = runNetwork n0 x
          (ys, n2) = runNetworkFeedback n f n1 (f y)
      in  (y :* ys, n2)

runNetworkFeedbackForever
    :: (Num (b i), Num (b o), BLASTensor b)
    => (b o -> b i)
    -> Network 'Recurrent b (i :~ c) hs o
    -> b i
    -> [b o]
runNetworkFeedbackForever f = go
  where
    go n0 x = y:ys
      where
        (y, n1) = runNetwork n0 x
        ys      = go n1 (f y)

data NetConf :: RunMode -> (BShape -> Type) -> LChain -> [LChain] -> BShape -> Type where
    NCExt :: ( ComponentLayer r c b i o
             , CConstr c b i o
             )
          => CConf c b i o
          -> NetConf r b (i :~ c) '[] o
    (:&~) :: ( ComponentLayer r c b i h
             , CConstr c b i h
             , SingI h
             , Num (b h)
             )
          => CConf c b i h
          -> NetConf r b (h :~ d) hs               o
          -> NetConf r b (i :~ c) ((h :~ d) ': hs) o

initNet
    :: forall b i c hs o m r.
     ( PrimMonad m
     , BLASTensor b
     , SingI i
     , SingI o
     )
    => NetConf r b (i :~ c) hs o
    -> Gen (PrimState m)
    -> m (Network r b (i :~ c) hs o)
initNet = \case
    NCExt c -> \g -> NetExt <$> initLayer sing sing c g
    c :&~ cN -> \g -> do
      l <- initLayer sing sing c g
      n <- initNet cN g
      return $ l :& n

data NetStruct :: RunMode -> (BShape -> Type) -> LChain -> [LChain] -> BShape -> Type where
    NSExt :: ( ComponentLayer r c b i o
             , CConstr c b i o
             )
          => NetStruct r b (i :~ c) '[] o
    NSInt :: ( SingI h
             , Num (b h)
             , ComponentLayer r c b i h
             , CConstr c b i h
             )
          => NetStruct r b (h :~ d) hs               o
          -> NetStruct r b (i :~ c) ((h :~ d) ': hs) o

defNetConf'
    :: NetStruct r b i hs o
    -> NetConf r b i hs o
defNetConf' = \case
    NSExt   -> NCExt defConf
    NSInt c -> defConf :&~ defNetConf' c

defNetConf
    :: Known (NetStruct r b i hs) o
    => NetConf r b i hs o
defNetConf = defNetConf' known

initDefNet'
    :: forall b i c hs o m r. (PrimMonad m, BLASTensor b, SingI i, SingI o)
    => NetStruct r b (i :~ c) hs o
    -> Gen (PrimState m)
    -> m (Network r b (i :~ c) hs o)
initDefNet' = initNet . defNetConf'

initDefNet
    :: (PrimMonad m, BLASTensor b, SingI i, SingI o, Known (NetStruct r b (i :~ c) hs) o)
    => Gen (PrimState m)
    -> m (Network r b (i :~ c) hs o)
initDefNet = initDefNet' known

instance (ComponentLayer r c b i o, CConstr c b i o)
        => Known (NetStruct r b (i :~ c) '[]) o where
    known = NSExt

instance ( SingI h
         , Num (b h)
         , ComponentLayer r c b i h
         , CConstr c b i h
         , Known (NetStruct r b (h :~ d) hs) o
         )
        => Known (NetStruct r b (i :~ c) ((h :~ d) ': hs)) o where
    known = NSInt known

data SomeNet :: RunMode -> (BShape -> Type) -> BShape -> BShape -> Type where
    SomeNet
        :: NetStruct r b (i :~ c) hs o
        -> Network r b (i :~ c) hs o
        -> SomeNet r b i o

someNet
    :: Known (NetStruct r b (i :~ c) hs) o
    => Network r b (i :~ c) hs o
    -> SomeNet r b i o
someNet = SomeNet known

instance (Known (NetStruct r b (i :~ c) hs) o)
            => Num (Network r b (i :~ c) hs o) where
    (+)           = liftNet2 (+) known
    (-)           = liftNet2 (-) known
    (*)           = liftNet2 (*) known
    negate        = liftNet negate known
    signum        = liftNet signum known
    abs           = liftNet abs    known
    fromInteger x = liftNet0 (fromInteger x) known

instance (Known (NetStruct r b (i :~ c) hs) o)
            => Fractional (Network r b (i :~ c) hs o) where
    (/)            = liftNet2 (/) known
    recip          = liftNet recip known
    fromRational x = liftNet0 (fromRational x) known

liftNet0
    :: forall r b i hs o. ()
    => (forall c n m.
            ( ComponentLayer r c b n m
            , CConstr c b n m
            )
            => Layer r c b n m
       )
    -> NetStruct r b i hs o
    -> Network r b i hs o
liftNet0 l = go
  where
    go  :: NetStruct r b j ks o
        -> Network   r b j ks o
    go = \case
      NSExt -> NetExt l
      NSInt s -> l :& go s

liftNet
    :: forall r b i hs o. ()
    => (forall c n m.
            ( ComponentLayer r c b n m
            , CConstr c b n m
            )
            => Layer r c b n m
            -> Layer r c b n m
       )
    -> NetStruct r b i hs o
    -> Network r b i hs o
    -> Network r b i hs o
liftNet f = go
  where
    go  :: NetStruct r b j ks o
        -> Network   r b j ks o
        -> Network   r b j ks o
    go = \case
      NSExt -> \case
        NetExt l -> NetExt (f l)
      NSInt s -> \case
        l :& n -> f l :& go s n

liftNet2
    :: forall r b i hs o. ()
    => (forall c n m.
            ( ComponentLayer r c b n m
            , CConstr c b n m
            )
            => Layer r c b n m
            -> Layer r c b n m
            -> Layer r c b n m
       )
    -> NetStruct r b i hs o
    -> Network r b i hs o
    -> Network r b i hs o
    -> Network r b i hs o
liftNet2 f = go
  where
    go  :: NetStruct r b j ks o
        -> Network   r b j ks o
        -> Network   r b j ks o
        -> Network   r b j ks o
    go = \case
      NSExt -> \case
        NetExt l1 -> \case
          NetExt l2 -> NetExt (f l1 l2)
      NSInt s -> \case
        l1 :& n1 -> \case
          l2 :& n2 -> f l1 l2 :& go s n1 n2

