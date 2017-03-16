{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module Learn.Neural (
  ) where

-- import           Type.Family.List
-- import           Type.Family.Maybe
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Option
import           GHC.TypeLits
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso    (Iso', iso)
import           Numeric.Backprop.Op
import           Statistics.Distribution
import           System.Random.MWC

type family MaybeToList (a :: Maybe k) = (b :: [k]) where
    MaybeToList ('Just a ) = '[a]
    MaybeToList 'Nothing   = '[]

-- type family StateInp (a :: Maybe (BShape Nat -> Type)) (s :: BShape Nat) = (b :: [Type]) where
--     StateInp ('Just t) s = StateInpjkk

class Component c b i o | c -> i, c -> o, c -> b where
    type CState  c b i o :: Maybe Type
    runComponent
        :: BPOp t (b i ': c b i o ': MaybeToList (CState c b i o))
                  (Tuple (b o ': MaybeToList (CState c b i o)))
    initComponent
        :: ContGen d
        => Sing i
        -> Sing o
        -> d
        -> Gen (PrimState m)
        -> m (c b i o, Option I (CState c b i o))

data NetState = SomeState
              | NoState

data NetComponent :: NetState -> (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type where
    NCPure
        :: (Component c b i o, CState c b i o ~ 'Nothing, Num (c b i o))
        => c b i o
        -> NetComponent s b i o
    NCStateful
        :: (Component c b i o, CState c b i o ~ 'Just st, Num (c b i o), Num st)
        => c b i o
        -> st
        -> NetComponent 'SomeState b i o

runNetComponent
    :: NetComponent st b i o
    -> b i
    -> (b o, NetComponent st b i o)
runNetComponent = \case
    n@(NCPure p)   -> \x -> (, n) . getI . head' $ evalBPOp runComponent (x ::< p ::< Ø)
    NCStateful p s -> \x -> case evalBPOp runComponent (x ::< p ::< s ::< Ø) of
      I y :< I s' :< Ø -> (y, NCStateful p s')

netComponentOp
    :: Num (b i)
    => OpB s '[ b i, NetComponent st b i o ] (Tuple '[b o, NetComponent st b i o])
netComponentOp = OpM $ \(I x :< I c :< Ø) ->
    case c of
      n@(NCPure p) -> do
        (I y :< Ø, gF) <- runOpM' (bpOp runComponent) (x ::< p ::< Ø)
        let out = y ::< n ::< Ø
            gF' = fmap (\case I y' :< I p' :< Ø -> y' ::< NCPure p' ::< Ø)
                . gF
                . fmap (\case x' :< _ :< Ø -> x' :< Ø)
        return (out, gF')
      NCStateful p s -> do
        (I y :< I s' :< Ø, gF) <- runOpM' (bpOp runComponent) (x ::< p ::< s ::< Ø)
        let out = y ::< NCStateful p s' ::< Ø
            gF' = fmap (\case I y' :< I p' :< I s'' :< Ø -> y' ::< NCStateful p' s'' ::< Ø)
                . gF
                . fmap (\case x' :< I _ :< Ø -> _)         -- here is the problem
        return (out, gF')


    -- -> b i
    -- -> ((b o, NetComponent st b i o), b o -> NetComponent st b i o)
-- gradNetComponent = \case
    -- n@(NCPure p) -> \x -> runST $ do
    --   (y :< Ø, gF) <- runOpM' (bpOp runComponent) (x ::< p ::< Ø)

-- netComponentOp
--     :: NetComponent st b i o
--     -> BPOp s '[ b i, NetComponent st b i o ] (b o)
-- netComponentOp = \case
--     NCPure p -> withInps $ \(x :< p' :< Ø) -> do
--         c :< Ø <- iso (\case NCPure p'' -> only_ p'') _ #<~ p'
--         _


data Network :: NetState -> (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type where
    NetExt :: NetComponent st b i o -> Network st b i o
    (:&)   :: NetComponent st b i h -> Network st b h o -> Network s b i o

runNetwork
    :: Network st b i o
    -> b i
    -> (b o, Network st b i o)
runNetwork = \case
    NetExt c -> second NetExt . runNetComponent c
    c :& n   -> \x -> case runNetComponent c x of
      (y, c') -> case runNetwork n y of
        (z, n') -> (z, c' :& n')


