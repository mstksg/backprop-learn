{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}

module Learn.Neural.Layer (
    MaybeToList
  , Component(..)
  , componentOpPure
  , HasState(..)
  , Layer(..)
  , layerOp
  , layerOpPure
  ) where


import           Control.Monad.Primitive
import           Data.Kind
import           Data.Singletons.Prelude
import           GHC.TypeLits
import           Numeric.BLAS
import           Data.Type.Util
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           System.Random.MWC
import           Type.Family.Constraint


class (SingI i, SingI o) => Component c i o where
    data CParam  c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Type
    type CState  c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Maybe Type
    type CConstr c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Constraint
    type CConstr c b i o = ØC
    data CConf   c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Type

    componentOp
        :: forall s b. (BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
        => OpB s (b i ': CParam c b i o ': MaybeToList (CState c b i o))
                 (b o ': MaybeToList (CState c b i o))
    initComponent
        :: (PrimMonad m, BLAS b, Tensor b, CConstr c b i o)
        => Sing i
        -> Sing o
        -> CConf c b i o
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

