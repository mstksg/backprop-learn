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
  , netOp
  , netOpPure
  , netOpRecurrent
  , netOpRecurrent_
  , netOpRecurrentLast
  , netOpRecurrentLast_
  , runNet
  , runNetPure
  , runNetRecurrent
  , runNetRecurrentLast
  , runNetFeedback
  , runNetFeedbackForever
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
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           System.Random.MWC
import           Type.Class.Known
import           Type.Class.Witness
import qualified Data.List.NonEmpty      as NE
import qualified Data.Type.Nat           as TCN


data LChain :: Type where
    (:~) :: [Nat] -> Type -> LChain

type s :~ c = s ':~ c

data Network :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    NetExt :: (ComponentLayer r c b i o, CConstr c b i o)
           => Layer r c b i o
           -> Network r b (i :~ c) '[] o
    (:&)   :: (ComponentLayer r c b i h, CConstr c b i h, Num (b h))
           => Layer r c b i h
           -> Network r b (h :~ d) hs               o
           -> Network r b (i :~ c) ((h :~ d) ': hs) o

netOp
    :: forall b i c hs o r s. (BLAS b, Num (b i), Num (b o))
    => OpB s '[ Network r b (i :~ c) hs o, b i ] '[ Network r b (i :~ c) hs o, b o ]
netOp = OpM $ \(I n :< I x :< Ø) -> case n of
    NetExt l -> do
      (I l' :< I y :< Ø, gF) <- runOpM' layerOp (l ::< x ::< Ø)
      let gF' = fmap (\case I dL :< I dX :< Ø -> NetExt dL ::< dX ::< Ø)
              . gF
              . (\case Just (NetExt dL) :< dY :< Ø -> Just dL :< dY :< Ø
                       Nothing          :< dY :< Ø -> Nothing :< dY :< Ø
                )
      return (NetExt l' ::< y ::< Ø, gF')
    (l :: Layer r c b i h) :& (n2 :: Network r b (h ':~ d) js o) -> do
      (I l'  :< I y :< Ø, gF ) <- runOpM' layerOp (l  ::< x ::< Ø)
      (I n2' :< I z :< Ø, gF') <- runOpM' netOp   (n2 ::< y ::< Ø)
      let gF'' :: Prod Maybe '[ Network r b (i ':~ c) ((h ':~ d) ': js) o, b o ]
               -> ST s (Tuple '[ Network r b (i ':~ c) ((h ':~ d) ': js) o, b i ])
          gF'' = \case Just (dL :& dN) :< dZ :< Ø -> do
                         I dN2 :< I dY :< Ø <- gF' (Just dN :< dZ :< Ø)
                         I dL0 :< I dX :< Ø <- gF  (Just dL :< Just dY :< Ø)
                         return $ (dL0 :& dN2) ::< dX ::< Ø
                       Nothing         :< dZ :< Ø -> do
                         I dN2 :< I dY :< Ø <- gF' (Nothing :< dZ      :< Ø)
                         I dL0 :< I dX :< Ø <- gF  (Nothing :< Just dY :< Ø)
                         return $ (dL0 :& dN2) ::< dX ::< Ø
      return ((l' :& n2') ::< z ::< Ø, gF'')

netOpPure
    :: forall b i c hs o s. (BLAS b, Num (b i), Num (b o))
    => OpB s '[ Network 'FeedForward b (i :~ c) hs o, b i ] '[ b o ]
netOpPure = OpM $ \(I n :< I x :< Ø) -> case n of
    NetExt l -> do
      (I y :< Ø, gF) <- runOpM' layerOpPure (l ::< x ::< Ø)
      let gF' = fmap (\case I dL :< I dX :< Ø -> NetExt dL ::< dX ::< Ø)
              . gF
      return (y ::< Ø, gF')
    (l :: Layer 'FeedForward c b i h) :& (n2 :: Network 'FeedForward b (h ':~ d) js o) -> do
      (I y :< Ø, gF ) <- runOpM' layerOpPure (l  ::< x ::< Ø)
      (I z :< Ø, gF') <- runOpM' netOpPure   (n2 ::< y ::< Ø)
      let gF'' :: Prod Maybe '[ b o ]
               -> ST s (Tuple '[ Network 'FeedForward b (i ':~ c) ((h ':~ d) ': js) o, b i])
          gF'' dZ = do
            I dN2 :< I dY :< Ø <- gF' dZ
            I dL0 :< I dX :< Ø <- gF  (Just dY :< Ø)
            return $ (dL0 :& dN2) ::< dX ::< Ø
      return (z ::< Ø, gF'')

netOpRecurrent
    :: forall n b i c hs o s.
     ( Known (NetStruct 'Recurrent b (i :~ c) hs) o
     , BLAS b
     , Num (b o)
     , Num (b i)
     )
    => TCN.Nat n
    -> OpB s (Network 'Recurrent b (i :~ c) hs o ': Replicate n (b i))
             (Network 'Recurrent b (i :~ c) hs o ': Replicate n (b o))
netOpRecurrent = \case
    TCN.Z_   -> idOp
    TCN.S_ n -> (replWit @_ @Num @(b i) n Wit //) $
                (replWit @_ @Num @(b o) n Wit //) $
                (replLen @_ @(b i) n          //) $
      bpOp . withInps $ \(n0 :< x :< xs) -> do
        n1 :< y  :< Ø <- netOp            ~$$ (n0 :< x :< Ø)
        n2 :< ys      <- netOpRecurrent n ~$$ (n1 :< xs)
        return (n2 :< y :< ys)

netOpRecurrent_
    :: forall n b i c hs o s.
     ( Known (NetStruct 'Recurrent b (i :~ c) hs) o
     , BLAS b
     , Num (b o)
     , Num (b i)
     )
    => TCN.Nat n
    -> OpB s (Network 'Recurrent b (i :~ c) hs o ': Replicate n (b i))
             (Replicate n (b o))
netOpRecurrent_ n = (replWit @_ @Num @(b i) n Wit //) $
                    (replWit @_ @Num @(b o) n Wit //) $
                    (replLen @_ @(b i) n          //) $
        bpOp . withInps $ \inps -> do
    _ :< ys <- netOpRecurrent n ~$$ inps
    return ys

netOpRecurrentLast
    :: forall n b i c hs o s.
     ( Known (NetStruct 'Recurrent b (i :~ c) hs) o
     , BLAS b
     , Num (b o)
     , Num (b i)
     )
    => TCN.Nat n
    -> OpB s (Network 'Recurrent b (i :~ c) hs o ': b i ': Replicate n (b i))
             '[Network 'Recurrent b (i :~ c) hs o, b o ]
netOpRecurrentLast = \case
    TCN.Z_ -> netOp
    TCN.S_ n -> (replWit @_ @Num @(b i) n Wit //) $
                (replLen @_ @(b i) n          //) $
      bpOp . withInps $ \(n0 :< x :< xs) -> do
        n1 :< _ :< Ø <- netOp                ~$$ (n0 :< x :< Ø)
        n2 :< y :< Ø <- netOpRecurrentLast n ~$$ (n1 :< xs)
        return (n2 :< y :< Ø)

netOpRecurrentLast_
    :: forall n b i c hs o s.
     ( Known (NetStruct 'Recurrent b (i :~ c) hs) o
     , BLAS b
     , Num (b o)
     , Num (b i)
     )
    => TCN.Nat n
    -> OpB s (Network 'Recurrent b (i :~ c) hs o ': b i ': Replicate n (b i))
            '[b o]
netOpRecurrentLast_ n = (replWit @_ @Num @(b i) n Wit //) $
                        (replLen @_ @(b i) n          //) $
        bpOp . withInps $ \inps -> do
    _ :< y :< Ø <- netOpRecurrentLast n ~$$ inps
    return $ only y

runNet
    :: (Num (b i), Num (b o), BLAS b)
    => Network r b (i :~ c) hs o
    -> b i
    -> (b o, Network r b (i :~ c) hs o)
runNet n x = case runOpB netOp (n ::< x ::< Ø) of
    I n' :< I y :< Ø -> (y, n')

runNetPure
    :: (Num (b i), Num (b o), BLAS b)
    => Network 'FeedForward b (i :~ c) hs o
    -> b i
    -> b o
runNetPure n x = case runOpB netOpPure (n ::< x ::< Ø) of
    I y :< Ø -> y

runNetRecurrent
    :: (Num (b i), Num (b o), BLAS b)
    => Network 'Recurrent b (i :~ c) hs o
    -> [b i]
    -> ([b o], Network 'Recurrent b (i :~ c) hs o)
runNetRecurrent n0 = \case
    []   -> ([], n0)
    x:xs -> let (y , n1) = runNet n0 x
                (ys, n2) = runNetRecurrent n1 xs
            in  (y:ys, n2)

runNetRecurrentLast
    :: (Num (b i), Num (b o), BLAS b)
    => Network 'Recurrent b (i :~ c) hs o
    -> NE.NonEmpty (b i)
    -> (b o, Network 'Recurrent b (i :~ c) hs o)
runNetRecurrentLast n0 (x NE.:| xs) = case xs of
    y:ys -> runNetRecurrentLast n1 (y NE.:| ys)
    []   -> (z, n1)
  where
    (z, n1) = runNet n0 x

runNetFeedback
    :: (Num (b i), Num (b o), BLAS b)
    => TCN.Nat n
    -> (b o -> b i)
    -> Network 'Recurrent b (i :~ c) hs o
    -> b i
    -> (VecT n b o, Network 'Recurrent b (i :~ c) hs o)
runNetFeedback = \case
    TCN.Z_   -> \_ n0 _ ->
      (ØV, n0)
    TCN.S_ n -> \f n0 x ->
      let (y , n1) = runNet n0 x
          (ys, n2) = runNetFeedback n f n1 (f y)
      in  (y :* ys, n2)

runNetFeedbackForever
    :: (Num (b i), Num (b o), BLAS b)
    => (b o -> b i)
    -> Network 'Recurrent b (i :~ c) hs o
    -> b i
    -> [b o]
runNetFeedbackForever f = go
  where
    go n0 x = y:ys
      where
        (y, n1) = runNet n0 x
        ~ys     = go n1 (f y)

data NetConf :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
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
     , BLAS b
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

data NetStruct :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
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
    :: forall b i c hs o m r. (PrimMonad m, BLAS b, SingI i, SingI o)
    => NetStruct r b (i :~ c) hs o
    -> Gen (PrimState m)
    -> m (Network r b (i :~ c) hs o)
initDefNet' = initNet . defNetConf'

initDefNet
    :: (PrimMonad m, BLAS b, SingI i, SingI o, Known (NetStruct r b (i :~ c) hs) o)
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

data SomeNet :: RunMode -> ([Nat] -> Type) -> [Nat] -> [Nat] -> Type where
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

