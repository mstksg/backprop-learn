{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Learn.Neural.Network.Dropout (
  ) where


import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Kind
import           Data.Type.Combinator
import           Data.Type.Product
import           GHC.TypeLits
import           Learn.Neural.Layer
import           Learn.Neural.Network
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Op
import           System.Random.MWC

data NetworkDO :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    NetExtDO
        :: (ComponentLayer r c b i o, CConstr c b i o)
        => Layer r c b i o
        -> NetworkDO r b (i :~ c) '[] o
    NetIntDO
        :: (ComponentLayer r c b i h, CConstr c b i h, Num (b h))
        => Double
        -> Layer r c b i h
        -> NetworkDO r b (h :~ d) hs               o
        -> NetworkDO r b (i :~ c) ((h :~ d) ': hs) o

-- TODO: should this multiply components
removeDropout
    :: NetworkDO r b i hs o
    -> Network r b i hs o
removeDropout = \case
    NetExtDO l     -> NetExt l
    NetIntDO _ l n -> l :& removeDropout n

addDropout
    :: Network r b i hs o
    -> Prod (C Double) hs
    -> NetworkDO r b i hs o
addDropout = \case
    NetExt l -> \case
      Ø -> NetExtDO l
    l :& n -> \case
      C r :< rs -> NetIntDO r l (addDropout n rs)

netOpDO
    :: forall b i c hs o r s. (BLAS b, Num (b i), Num (b o))
    => OpB s '[ NetworkDO r b (i :~ c) hs o, b i ] '[ NetworkDO r b (i :~ c) hs o, b o ]
netOpDO = OpM $ \(I n :< I x :< Ø) -> case n of
    NetExtDO l -> do
      (I l' :< I y :< Ø, gF) <- runOpM' layerOp (l ::< x ::< Ø)
      let gF' = fmap (\case I dL :< I dX :< Ø -> NetExt dL ::< dX ::< Ø)
              . gF
              . (\case Just (NetExt dL) :< dY :< Ø -> Just dL :< dY :< Ø
                       Nothing          :< dY :< Ø -> Nothing :< dY :< Ø
                )
      return (NetExt l' ::< y ::< Ø, gF')
    NetIntDO r (l :: Layer r c b i h) (n2 :: NetworkDO r b (h ':~ d) js o) -> do
      (I l'  :< I y :< Ø, gF ) <- runOpM' layerOp (l  ::< x ::< Ø)
      (I n2' :< I z :< Ø, gF') <- runOpM' netOpDO   (n2 ::< y ::< Ø)
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
      return ((NetIntDO r l' n2') ::< z ::< Ø, gF'')

