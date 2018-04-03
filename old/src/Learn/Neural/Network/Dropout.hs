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
  , netOpDOPure
  , konstDO, konstDO', mapDO, mapDO'
  , alongNet
  ) where


import           Control.Monad.Primitive
import           Data.Bool
import           Data.Kind
import           Data.Singletons
import           Data.Traversable
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

-- | For something like
--
-- @
-- l1 ':&' l2 :& 'NetExt' l3
-- @
--
-- you could have
--
-- @
-- 0.2 ':&%' 0.3 :&% DOExt
-- @
--
-- Would would represent a 20% dropout after @l1@ and a 30% dropout after
-- @l2@.  By conscious design decision, 'DOExt' does not take any dropout
-- rate, and it is therefore impossible to have dropout after the final
-- layer before the output.  It is also not possible to have dropout before
-- the first layer, after the input.
data Dropout :: RunMode -> ([Nat] -> Type) -> LChain -> [LChain] -> [Nat] -> Type where
    DOExt
        :: Dropout r b (i :~ c) '[] o
    (:&%)
        :: (Num (b h), SingI h)
        => !(Maybe Double)
        -> !(Dropout r b (h :~ d) hs o)
        -> Dropout r b (i :~ c) ((h :~ d) ': hs) o

infixr 4 :&%

alongNet
    :: n r b i hs o
    -> Dropout r b i hs o
    -> Dropout r b i hs o
alongNet _ d = d

konstDO
    :: forall r b i hs o. ()
    => NetStruct r b i hs o
    -> Maybe Double
    -> Dropout r b i hs o
konstDO s0 x = go s0
  where
    go :: NetStruct r b j js o -> Dropout r b j js o
    go = \case
      NSExt   -> DOExt
      NSInt s -> x :&% go s

konstDO'
    :: forall r b i hs o. Known (NetStruct r b i hs) o
    => Maybe Double
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
      x :&% d -> fmap f x :&% go d
      
mapDO'
    :: forall r b i hs o. ()
    => (Maybe Double -> Maybe Double)
    -> Dropout r b i hs o
    -> Dropout r b i hs o
mapDO' f = go
  where
    go :: Dropout r b j js o -> Dropout r b j js o
    go = \case
      DOExt   -> DOExt
      x :&% d -> f x :&% go d
      
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
      mask <- forM r $ \r' ->
        genA @b (sing @_ @h) $ \_ -> bool (1 / (1 - realToFrac r')) 0 <$> bernoulli r' g
      no :: OpBS '[ Network r b (h :~ d) js o, b h ] '[ Network r b (h :~ d) js o, b o ]
            <- netOpDO @m @b @h @d @js @o @r d g
      return $ OpBS $ OpM $ \(I n :< I x :< Ø) -> case n of
        (l :: Layer r c b i h) :& (n2 :: Network r b (h ':~ d) js o) -> do
          (I l'  :< I y :< Ø, gF ) <- runOpM' (layerOp @r @c @i @h @b) (l  ::< x ::< Ø)
          (I n2' :< I z :< Ø, gF') <- runOpM' (runOpBS no            ) (n2 ::< y ::< Ø)
          let gF'' = \case Just (dL :& dN) :< dZ :< Ø -> do
                             I dN2 :< I dY :< Ø <- gF' (Just dN :< dZ       :< Ø)
                             let dY' = maybe dY (tzip (*) dY) mask
                             I dL0 :< I dX :< Ø <- gF  (Just dL :< Just dY' :< Ø)
                             return $ (dL0 :& dN2) ::< dX ::< Ø
                           Nothing         :< dZ :< Ø -> do
                             I dN2 :< I dY :< Ø <- gF' (Nothing :< dZ       :< Ø)
                             let dY' = maybe dY (tzip (*) dY) mask
                             I dL0 :< I dX :< Ø <- gF  (Nothing :< Just dY' :< Ø)
                             return $ (dL0 :& dN2) ::< dX ::< Ø
          return ((l' :& n2') ::< z ::< Ø, gF'')

netOpDOPure
    :: forall m b i c hs o. (BLAS b, Num (b i), Num (b o), PrimMonad m, SingI o)
    => Dropout 'FeedForward b (i :~ c) hs o
    -> Gen (PrimState m)
    -> m (OpBS '[ Network 'FeedForward b (i :~ c) hs o, b i ] '[ b o ])
netOpDOPure = \case
    DOExt -> \_ -> return $ OpBS $ OpM $ \(I n :< I x :< Ø) -> case n of
      NetExt (l :: Layer 'FeedForward c b i o) -> do
        (I y :< Ø, gF) <- runOpM' (layerOpPure @c @i @o @b) (l ::< x ::< Ø)
        let gF' = fmap (\case I dL :< I dX :< Ø -> NetExt dL ::< dX ::< Ø)
                . gF
        return (y ::< Ø, gF')
    r :&% (d :: Dropout 'FeedForward b (h :~ d) js o) -> \g -> do
      mask <- forM r $ \r' ->
        genA @b (sing @_ @h) $ \_ -> bool (1 / (1 - realToFrac r')) 0 <$> bernoulli r' g
      no :: OpBS '[ Network 'FeedForward b (h :~ d) js o, b h ] '[ b o ]
            <- netOpDOPure @m @b @h @d @js @o d g
      return $ OpBS $ OpM $ \(I n :< I x :< Ø) -> case n of
        (l :: Layer 'FeedForward c b i h) :& (n2 :: Network 'FeedForward b (h ':~ d) js o) -> do
          (I y :< Ø, gF ) <- runOpM' (layerOpPure @c @i @h @b) (l  ::< x ::< Ø)
          (I z :< Ø, gF') <- runOpM' (runOpBS no             ) (n2 ::< y ::< Ø)
          let gF'' dZ = do
                I dN2 :< I dY :< Ø <- gF' dZ
                let dY' = maybe dY (tzip (*) dY) mask
                I dL0 :< I dX :< Ø <- gF (Just dY' :< Ø)
                return $ (dL0 :& dN2) ::< dX ::< Ø
          return (z ::< Ø, gF'')
