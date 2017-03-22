{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module Learn.Neural.Layer (
    MaybeToList
  , Component(..)
  , StateWit(..)
  , componentOpPure
  , HasState(..)
  , Layer(..)
  , layerOp
  , layerOpPure
  , initLayer
  ) where


import           Control.Monad.Primitive
import           Data.Kind
import           Data.Singletons.Prelude
import           Data.Type.Util
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           Numeric.Tensor
import           System.Random.MWC
import           Type.Class.Known
import           Type.Family.Constraint

data HasState = NoState
              | SomeState

data StateWit :: Maybe k -> HasState -> Type where
    SWPure  :: StateWit 'Nothing  r
    SWState :: StateWit ('Just a) 'SomeState

class (SingI i, SingI o)
      => Component (c :: Type)
                   (b :: BShape -> Type)
                   (i :: BShape)
                   (o :: BShape)
        where
    data CParam  c b i o :: Type
    type CState  c b i o :: Maybe Type
    type CConstr c b i o :: Constraint
    type CConstr c b i o = ØC
    data CConf   c b i o :: Type

    componentOp
        :: forall s. (BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
        => OpB s (b i ': CParam c b i o ': MaybeToList (CState c b i o))
                 (b o ': MaybeToList (CState c b i o))
    initComponent
        :: forall m. (PrimMonad m, BLAS b, Tensor b, CConstr c b i o)
        => Sing i
        -> Sing o
        -> CConf c b i o
        -> Gen (PrimState m)
        -> m (Tuple (CParam c b i o ': MaybeToList (CState c b i o)))

    defConf :: CConf c b i o

    componentStateWit :: forall r. StateWit (CState c b i o) r

instance Known (StateWit 'Nothing) r where
    known = SWPure

instance Known (StateWit ('Just a)) 'SomeState where
    known = SWState

componentOpPure
    :: forall c b i o s.
     ( Component c b i o
     , CState c b i o ~ 'Nothing
     , BLAS b
     , Tensor b
     , Num (b i)
     , Num (b o)
     , CConstr c b i o
     )
    => OpB s '[ b i, CParam c b i o ] '[ b o ]
componentOpPure = componentOp @c @b @i @o

data Layer :: HasState -> Type -> (BShape -> Type) -> BShape -> BShape -> Type where
    LPure  :: (CState c b i o ~ 'Nothing) => CParam c b i o -> Layer r c b i o
    LState :: (CState c b i o ~ 'Just s ) => CParam c b i o -> s -> Layer 'SomeState c b i o

instance Num (Layer r c b i o)

layerOp
    :: forall c b i o r s. (Component c b i o, BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
    => OpB s '[ b i, Layer r c b i o ] '[ b o, Layer r c b i o ]
layerOp = OpM $ \(I x :< I l :< Ø) -> case l of
    LPure p -> do
      (I y :< Ø, gF) <- runOpM' (componentOp @_ @b) (x ::< p ::< Ø)
      -- let gF' = _ . lPure . _ $ gF
      let gF' = fmap (\case I dX :< I dP :< Ø -> I dX :< I (LPure dP) :< Ø)
              . gF
              . (\case dY :< _ :< Ø -> dY :< Ø)
      return (y ::< LPure p ::< Ø, gF')
    LState p s -> do
      (I y :< I s' :< Ø, gF) <- runOpM' (componentOp @_ @b) (x ::< p ::< s ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< I dS :< Ø -> dX ::< LState dP dS ::< Ø)
              . gF
              . (\case dY :< Just (LState _ dS) :< Ø -> dY :< Just dS :< Ø
                       dY :< Nothing            :< Ø -> dY :< Nothing :< Ø
                )
      return (y ::< LState p s' ::< Ø, gF')

layerOpPure
    :: forall c b i o s. (Component c b i o, BLAS b, Tensor b, Num (b i), Num (b o), CConstr c b i o)
    => OpB s '[ b i, Layer 'NoState c b i o ] '[ b o ]
layerOpPure = OpM $ \(I x :< I l :< Ø) -> case l of
    LPure p -> do
      (I y :< Ø, gF) <- runOpM' (componentOp @_ @b) (x ::< p ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< Ø -> I dX :< I (LPure dP) :< Ø)
              . gF
      return (y ::< Ø, gF')

initLayer
    :: forall c b i o m r. (PrimMonad m, BLAS b, Tensor b, CConstr c b i o, Component c b i o)
    => Sing i
    -> Sing o
    -> CConf c b i o
    -> Gen (PrimState m)
    -> m (Layer r c b i o)
initLayer si so conf = case componentStateWit @c @b @i @o @r of
    SWPure  -> \g -> LPure . getI . head' <$> initComponent @_ @b si so conf g
    SWState -> \g -> do
      I p :< I s :< Ø <- initComponent @_ @b si so conf g
      return $ LState p s

