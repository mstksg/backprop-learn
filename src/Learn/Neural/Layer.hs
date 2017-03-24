{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE Strict                 #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Learn.Neural.Layer (
    Component(..)
  , ComponentFF(..)
  , componentOpDefault
  , RunMode(..)
  , Layer(..)
  , RunModeWit(..)
  , ComponentLayer(..)
  , layerOp
  , layerOpPure
  , initLayer
  ) where


import           Control.Monad.Primitive
import           Data.Kind
import           Data.Singletons.Prelude
import           Numeric.BLASTensor
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           System.Random.MWC
import           Type.Family.Constraint

data RunMode = FeedForward
             | Recurrent

data RunModeWit :: RunMode -> Type -> (BShape -> Type) -> BShape -> BShape -> Type where
    RMIsFF  :: ComponentFF c b i o => RunModeWit r c b i o
    RMNotFF :: RunModeWit 'Recurrent c b i o

class (Fractional (CParam c b i o), Fractional (CState c b i o), BLASTensor b)
        => Component (c :: Type) (b :: BShape -> Type) (i :: BShape) (o :: BShape) where
    data CParam  c b i o :: Type
    data CState  c b i o :: Type
    type CConstr c b i o :: Constraint
    type CConstr c b i o = ØC
    data CConf   c b i o :: Type

    componentOp
        :: forall s. (Num (b i), Num (b o), CConstr c b i o)
        => OpB s '[ b i, CParam c b i o, CState c b i o ]
                 '[ b o, CState c b i o ]

    initParam
        :: forall m. (PrimMonad m, CConstr c b i o)
        => Sing i
        -> Sing o
        -> CConf c b i o
        -> Gen (PrimState m)
        -> m (CParam c b i o)

    initState
        :: forall m. (PrimMonad m, CConstr c b i o)
        => Sing i
        -> Sing o
        -> CConf c b i o
        -> Gen (PrimState m)
        -> m (CState c b i o)

    defConf :: CConf c b i o

class Component c b i o => ComponentFF c b i o where
    componentOpFF
        :: forall s. (Num (b i), Num (b o), CConstr c b i o)
        => OpB s '[ b i, CParam c b i o ] '[ b o ]

componentOpDefault
    :: forall c b i o s.
     ( ComponentFF c b i o
     , BLASTensor b
     , Num (b i)
     , Num (b o)
     , CConstr c b i o
     , Num (CParam c b i o)
     , Num (CState c b i o)
     )
    => OpB s '[ b i, CParam c b i o, CState c b i o ]
             '[ b o, CState c b i o ]
componentOpDefault = bpOp . withInps $ \(x :< p :< s :< Ø) -> do
    y <- componentOpFF ~$ (x :< p :< Ø)
    return $ y :< s :< Ø

class Component c b i o => ComponentLayer (r :: RunMode) c b i o where
    componentRunMode :: RunModeWit r c b i o

data Layer :: RunMode -> Type -> (BShape -> Type) -> BShape -> BShape -> Type where
    LFeedForward
        :: ComponentFF c b i o
        => CParam c b i o
        -> Layer r c b i o
    LRecurrent
        :: CParam c b i o
        -> CState c b i o
         -> Layer 'Recurrent c b i o

instance ComponentLayer r c b i o => Num (Layer r c b i o) where
    (+) = liftLayer2 (+) (+)
    (-) = liftLayer2 (-) (-)
    (*) = liftLayer2 (*) (*)
    negate = liftLayer negate negate
    signum = liftLayer signum signum
    abs    = liftLayer abs    abs
    fromInteger x  = case componentRunMode @r @c @b @i @o of
      RMIsFF  -> LFeedForward (fromInteger x)
      RMNotFF -> LRecurrent   (fromInteger x) (fromInteger x)

instance ComponentLayer r c b i o => Fractional (Layer r c b i o) where
    (/) = liftLayer2 (/) (/)
    recip = liftLayer recip recip
    fromRational x  = case componentRunMode @r @c @b @i @o of
      RMIsFF  -> LFeedForward (fromRational x)
      RMNotFF -> LRecurrent   (fromRational x) (fromRational x)

liftLayer
    :: (CParam c b i o -> CParam c b i o)
    -> (CState c b i o -> CState c b i o)
    -> Layer r c b i o
    -> Layer r c b i o
liftLayer f g = \case
    LFeedForward p -> LFeedForward (f p)
    LRecurrent p s -> LRecurrent (f p) (g s)

liftLayer2
    :: (CParam c b i o -> CParam c b i o -> CParam c b i o)
    -> (CState c b i o -> CState c b i o -> CState c b i o)
    -> Layer r c b i o
    -> Layer r c b i o
    -> Layer r c b i o
liftLayer2 f g = \case
    LFeedForward p1 -> \case
      LFeedForward p2 -> LFeedForward (f p1 p2)
      LRecurrent p2 _ -> LFeedForward (f p1 p2)
    LRecurrent p1 s1 -> \case
      LFeedForward p2  -> LFeedForward (f p1 p2)
      LRecurrent p2 s2 -> LRecurrent (f p1 p2) (g s1 s2)

layerOp
    :: forall r c i o b s. (Component c b i o, BLASTensor b, Num (b i), Num (b o), CConstr c b i o)
    => OpB s '[ b i, Layer r c b i o ] '[ b o, Layer r c b i o ]
layerOp = OpM $ \(I x :< I l :< Ø) -> case l of
    LFeedForward p -> do
      (I y :< Ø, gF) <- runOpM' componentOpFF (x ::< p ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< Ø -> I dX :< I (LFeedForward dP) :< Ø)
              . gF
              . (\case dY :< _ :< Ø -> dY :< Ø)
      return (y ::< LFeedForward p ::< Ø, gF')
    LRecurrent p s -> do
      (I y :< I s' :< Ø, gF) <- runOpM' (componentOp @c @b) (x ::< p ::< s ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< I dS :< Ø -> dX ::< LRecurrent dP dS ::< Ø)
              . gF
              . (\case dY :< Just (LRecurrent _ dS) :< Ø -> dY :< Just dS :< Ø
                       dY :< Just (LFeedForward _)  :< Ø -> dY :< Nothing :< Ø
                       dY :< Nothing                :< Ø -> dY :< Nothing :< Ø
                )
      return (y ::< LRecurrent p s' ::< Ø, gF')

layerOpPure
    :: forall c i o b s. (Component c b i o, BLASTensor b, Num (b i), Num (b o), CConstr c b i o)
    => OpB s '[ b i, Layer 'FeedForward c b i o ] '[ b o ]
layerOpPure = OpM $ \(I x :< I l :< Ø) -> case l of
    LFeedForward p -> do
      (I y :< Ø, gF) <- runOpM' componentOpFF (x ::< p ::< Ø)
      let gF' = fmap (\case I dX :< I dP :< Ø -> I dX :< I (LFeedForward dP) :< Ø)
              . gF
      return (y ::< Ø, gF')

initLayer
    :: forall r c b i o m.
     ( PrimMonad m
     , BLASTensor b
     , ComponentLayer r c b i o
     , CConstr c b i o
     )
    => Sing i
    -> Sing o
    -> CConf c b i o
    -> Gen (PrimState m)
    -> m (Layer r c b i o)
initLayer si so conf g = case componentRunMode @r @c @b @i @o of
    RMIsFF  -> LFeedForward <$> initParam @c @b si so conf g
    RMNotFF -> do
      p <- initParam @c @b si so conf g
      s <- initState @c @b si so conf g
      return $ LRecurrent p s

