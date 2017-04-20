{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE Strict               #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Learn.Neural.Network.Dropout (
    Dropout(..)
  , NetworkDO(..)
  , netOpDO
  , konstDO, konstDO', mapDO, zipDO
  ) where


import           Control.Monad.Primitive
import           Data.Bool
import           Data.Kind
import           Data.Singletons
import           Data.Type.Combinator
import           Data.Type.Product
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Learn.Neural.Network
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           System.Random.MWC
import           System.Random.MWC.Distributions
import           Type.Class.Known

data NetworkDO :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    NDO :: { ndoDropout :: !(Dropout r b i hs o)
           , ndoNetwork :: !(Network r b i hs o)
           }
        -> NetworkDO r b i hs o

data Dropout :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    DOExt
        :: Dropout r b (i :~ c) '[] o
    (:&%)
        :: (Num (b h), SingI h)
        => !Double
        -> !(Dropout r b (h :~ d) hs o)
        -> Dropout r b (i :~ c) ((h :~ d) ': hs) o

instance Known (NetStruct r b (i :~ c) hs) o => Num (Dropout r b (i :~ c) hs o) where
    (+) = zipDO (+)
    (-) = zipDO (-)
    (*) = zipDO (*)
    negate = mapDO negate
    signum = mapDO signum
    abs    = mapDO abs
    fromInteger = konstDO' . fromInteger

konstDO
    :: forall r b i hs o. ()
    => NetStruct r b i hs o
    -> Double
    -> Dropout r b i hs o
konstDO s0 x = go s0
  where
    go :: NetStruct r b j js o -> Dropout r b j js o
    go = \case
      NSExt   -> DOExt
      NSInt s -> x :&% go s

konstDO'
    :: forall r b i hs o. Known (NetStruct r b i hs) o
    => Double
    -> Dropout r b i hs o
konstDO' = konstDO known

mapDO
    :: forall r b i hs o. ()
    => (Double -> Double)
    -> Dropout r b i hs o
    -> Dropout r b i hs o
mapDO f = go
  where
    go :: Dropout r b j js o -> Dropout r b j js o
    go = \case
      DOExt   -> DOExt
      x :&% d -> f x :&% go d
      
zipDO
    :: forall r b i hs o. ()
    => (Double -> Double -> Double)
    -> Dropout r b i hs o
    -> Dropout r b i hs o
    -> Dropout r b i hs o
zipDO f = go
  where
    go :: Dropout r b j js o -> Dropout r b j js o -> Dropout r b j js o
    go = \case
      DOExt -> \case
        DOExt -> DOExt
      x :&% dx -> \case
        y :&% dy -> f x y :&% go dx dy
      
netOpDO
    :: forall m b i c hs o r. (BLAS b, Num (b i), Num (b o), PrimMonad m, SingI o)
    => Dropout r b (i :~ c) hs o
    -> Gen (PrimState m)
    -> m (OpBS '[ Network r b (i :~ c) hs o, b i ] '[ Network r b (i :~ c) hs o, b o ])
netOpDO = \case
    DOExt -> \_ -> return $ OpBS $ OpM $ \(I n :< I x :< Ø) -> case n of
      NetExt (l :: Layer r c b i o) -> do
        (I l' :< I y :< Ø, gF) <- runOpM' (layerOp @r @c @i @o @b) (l ::< x ::< Ø)
        let gF' = fmap (\case I dL :< I dX :< Ø -> NetExt dL ::< dX ::< Ø)
                . gF
                . (\case Just (NetExt dL) :< dY :< Ø ->
                           Just dL :< dY :< Ø
                         Nothing          :< dY :< Ø ->
                           Nothing :< dY :< Ø
                  )
        return (NetExt l' ::< y ::< Ø, gF')
    r :&% (d :: Dropout r b (h :~ d) js o) -> \g -> do
      mask <- genA @b (sing @_ @h) $ \_ -> bool (1 / (1 - realToFrac r)) 0 <$> bernoulli r g
      no :: OpBS '[ Network r b (h :~ d) js o, b h ] '[ Network r b (h :~ d) js o, b o ]
            <- netOpDO @m @b @h @d @js @o @r d g
      return $ OpBS $ OpM $ \(I n :< I x :< Ø) -> case n of
        (l :: Layer r c b i h) :& (n2 :: Network r b (h ':~ d) js o) -> do
          (I l'  :< I y :< Ø, gF ) <- runOpM' (layerOp @r @c @i @h @b) (l  ::< x ::< Ø)
          (I n2' :< I z :< Ø, gF') <- runOpM' (runOpBS no            ) (n2 ::< y ::< Ø)
          let gF'' = \case Just (dL :& dN) :< dZ :< Ø -> do
                             I dN2 :< I dY :< Ø <- gF' (Just dN :< dZ       :< Ø)
                             let dY' = tzip (*) mask dY
                             I dL0 :< I dX :< Ø <- gF  (Just dL :< Just dY' :< Ø)
                             return $ (dL0 :& dN2) ::< dX ::< Ø
                           Nothing         :< dZ :< Ø -> do
                             I dN2 :< I dY :< Ø <- gF' (Nothing :< dZ       :< Ø)
                             let dY' = tzip (*) mask dY
                             I dL0 :< I dX :< Ø <- gF  (Nothing :< Just dY' :< Ø)
                             return $ (dL0 :& dN2) ::< dX ::< Ø
          return ((l' :& n2') ::< z ::< Ø, gF'')
