{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Learn.Neural.Network.Dropout (
    Dropout(..)
  , NetworkDO(..)
  , netOpDO
  ) where


import           Control.Monad.Primitive
import           Control.Monad.ST
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

data NetworkDO :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    NDO :: { ndoDropout :: !(Dropout r b i hs o)
           , ndoNetwork :: !(Network r b i hs o)
           }
        -> NetworkDO r b i hs o

data Dropout :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    DOExt
        :: !Double
        -> Dropout r b (i :~ c) '[] o
    (:&%)
        :: (Num (b h), SingI h)
        => !Double
        -> !(Dropout r b (h :~ d) hs o)
        -> Dropout r b (i :~ c) ((h :~ d) ': hs) o

netOpDO
    :: forall m b i c hs o r s. (BLAS b, Num (b i), Num (b o), PrimMonad m, SingI o)
    => Dropout r b (i :~ c) hs o
    -> Gen (PrimState m)
    -> m (OpB s '[ Network r b (i :~ c) hs o, b i ] '[ Network r b (i :~ c) hs o, b o ])
netOpDO = \case
    DOExt r -> \g -> do
      mask <- genA @b (sing @_ @o) $ \_ -> bool (1 / (1 - realToFrac r)) 0 <$> bernoulli r g
      return . OpM $ \(I n :< I x :< Ø) -> case n of
        NetExt (l :: Layer r c b i o) -> do
          (I l' :< I y :< Ø, gF) <- runOpM' (layerOp @r @c @i @o @b @s) (l ::< x ::< Ø)
          let y' = tzip (*) mask y
              gF' = fmap (\case I dL :< I dX :< Ø -> NetExt dL ::< dX ::< Ø)
                  . gF
                  . (\case Just (NetExt dL) :< dY :< Ø ->
                             Just dL :< Just (maybe mask (tzip (*) mask) dY) :< Ø
                           Nothing          :< dY :< Ø ->
                             Nothing :< Just (maybe mask (tzip (*) mask) dY) :< Ø
                    )
          return (NetExt l' ::< y' ::< Ø, gF')
    r :&% (d :: Dropout r b (h :~ d) js o) -> \g -> do
      mask <- genA @b (sing @_ @h) $ \_ -> bool (1 / (1 - realToFrac r)) 0 <$> bernoulli r g
      no   <- netOpDO @m @b @h @d @js @o @r @s d g
      return . OpM $ \(I n :< I x :< Ø) -> case n of
        (l :: Layer r c b i h) :& (n2 :: Network r b (h ':~ d) js o) -> do
          (I l'  :< I y :< Ø, gF ) <- runOpM' (layerOp @r @c @i @h @b @s) (l  ::< x ::< Ø)
          (I n2' :< I z :< Ø, gF') <- runOpM' no      (n2 ::< y ::< Ø)
          let gF'' :: Prod Maybe '[ Network r b (i ':~ c) ((h ':~ d) ': js) o, b o ]
                   -> ST s (Tuple '[ Network r b (i ':~ c) ((h ':~ d) ': js) o, b i ])
              gF'' = \case Just (dL :& dN) :< dZ :< Ø -> do
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
