{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}

module Learn.Neural
  where

import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Bifunctor
import           Data.Kind
import           Data.Singletons.Prelude
import           Data.Type.Index
import           Data.Type.Option
import           GHC.TypeLits
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso    (Iso', iso, from, tup1)
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           Statistics.Distribution
import           System.Random.MWC
import           Type.Family.Bool
import           Type.Family.Constraint

type family MaybeToList (a :: Maybe k) = (b :: [k]) | b -> a where
    MaybeToList ('Just a ) = '[a]
    MaybeToList 'Nothing   = '[]

class (SingI i, SingI o) => Component c i o where
    data CParam  c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Type
    type CState  c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Maybe Type
    type CConstr c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Constraint
    type CConstr c b i o = ØC

    componentOp
        :: forall s b. (BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
        => OpB s (b i ': CParam c b i o ': MaybeToList (CState c b i o))
                 (b o ': MaybeToList (CState c b i o))
    initComponent
        :: (PrimMonad m, BLAS b, Tensor b, CConstr c b i o)
        => Sing i
        -> Sing o
        -> Gen (PrimState m)
        -> m (Tuple (CParam c b i o ': MaybeToList (CState c b i o)))

componentOpPure
    :: forall c i o s b.
     ( Component c i o
     , CState c b i o ~ 'Nothing
     , BLAS b
     , Tensor b
     , Num (b i)
     , Num (b o)
     , CConstr c b i o
     )
    => OpB s '[ b i, CParam c b i o ] '[ b o ]
componentOpPure = componentOp

data HasState = NoState
              | SomeState

data Layer :: Type -> HasState -> (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type where
    LPure  :: (CState c b i o ~ 'Nothing) => CParam c b i o -> Layer c r b i o
    LState :: (CState c b i o ~ 'Just s ) => CParam c b i o -> s -> Layer c 'SomeState b i o

instance Num (Layer c r b i o)

layerOp
    :: forall s c r b i o. (Component c i o, BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
    => OpB s '[ b i, Layer c r b i o ] '[ b o, Layer c r b i o ]
layerOp = OpM $ \(I x :< I l :< Ø) -> case l of
    LPure p -> do
      (I y :< Ø, gF) <- runOpM' (componentOp @_ @_ @o) (x ::< p ::< Ø)
      -- let gF' = _ . lPure . _ $ gF
      let gF' = fmap (\case I dX :< I dP :< Ø -> I dX :< I (LPure dP) :< Ø)
              . gF
              . (\case dY :< _ :< Ø -> dY :< Ø)
      return (y ::< LPure p ::< Ø, gF')
    LState p s -> do
      (I y :< I s' :< Ø, gF) <- runOpM' (componentOp @_ @_ @o) (x ::< p ::< s ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< I dS :< Ø -> dX ::< LState dP dS ::< Ø)
              . gF
              . (\case dY :< Just (LState _ dS) :< Ø -> dY :< Just dS :< Ø
                       dY :< Nothing            :< Ø -> dY :< Nothing :< Ø
                )
      return (y ::< LState p s' ::< Ø, gF')

layerOpPure
    :: forall s c b i o. (Component c i o, BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
    => OpB s '[ b i, Layer c 'NoState b i o ] '[ b o ]
layerOpPure = OpM $ \(I x :< I l :< Ø) -> case l of
    LPure p -> do
      (I y :< Ø, gF) <- runOpM' (componentOp @_ @_ @o) (x ::< p ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< Ø -> I dX :< I (LPure dP) :< Ø)
              . gF
      return (y ::< Ø, gF')

data LChain :: Type where
    (:~) :: BShape Nat -> Type -> LChain

data Network :: HasState -> (BShape Nat -> Type) -> LChain -> [LChain] -> BShape Nat -> Type where
    NetExt :: Layer c r b i o
           -> Network r b (i ':~ c) '[] o
    (:&)   :: (Num (b h), Component c i h, Component d h o, CConstr c b i h, CConstr d b h o)
           => Layer c r b i h
           -> Network r b (h ':~ d) hs               o
           -> Network r b (i ':~ c) ((h ':~ d) ': hs) o

networkOp
    :: forall s r b i c hs o. (Component c i o, BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
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
    :: forall s b i c hs o. (Component c i o, BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
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
