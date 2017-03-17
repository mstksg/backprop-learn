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
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}

module Learn.Neural (
  ) where

-- import           Type.Family.List
-- import           Type.Family.Maybe
import           Control.Monad.Primitive
import           Control.Monad.ST
import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Index
import           Data.Type.Option
import           GHC.TypeLits
import           Numeric.BLAS
import           Numeric.Backprop
import           Numeric.Backprop.Iso    (Iso', iso)
import           Numeric.Backprop.Op
import           Statistics.Distribution
import           System.Random.MWC
import           Type.Family.Bool

type family MaybeToList (a :: Maybe k) = (b :: [k]) where
    MaybeToList ('Just a ) = '[a]
    MaybeToList 'Nothing   = '[]

-- type family StateInp (a :: Maybe (BShape Nat -> Type)) (s :: BShape Nat) = (b :: [Type]) where
--     StateInp ('Just t) s = StateInp

-- data Statefulness = Stateful
--                   | NonStateful

class Component c where
    initComponent
        :: ContGen d
        => Sing i
        -> Sing o
        -> d
        -> Gen (PrimState m)
        -> m (c b i o)

class Component c => ComponentP c where
    runComponentP :: OpB t '[b i, c b i o] (b o)

class Component c => ComponentS c where
    runComponentS :: OpB t '[b i, c b i o] (Tuple '[b o, c b i o])

data NetComponent :: (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type where
    NCPure     :: (Num (c b i o), ComponentP c) => c b i o -> NetComponent b i o
    NCStateful :: ComponentS c => c b i o -> NetComponent b i o

runNetComponent
    :: Num (b o)
    => BPOp s '[b i, NetComponent b i o] (Tuple '[ b o, NetComponent b i o ])
runNetComponent = withInps $ \(x :< c :< Ø) ->
    withGADT c $ \case
      c'@(NCPure p) -> BPC (only_ p) (NCPure . getI . head') $ \(pVar :< Ø) -> do
        y   <- runComponentP ~$ (x :< pVar :< Ø)
        out :< Ø <- isoVar _ (y :< constVar c' :< Ø)
        return out

-- --       c'@(NCPure p) -> BPC (p ::< Ø) (NCPure . getI . head') $ \(pVar :< Ø) -> do
-- --         y :< Ø <- runComponent ~$$ (x :< pVar :< Ø)
-- --         return $ y :< constVar c' :< Ø

-- class ComponentPure c b i o | c -> i, c -> o, c -> b where

-- class Component c sf b i o | c -> i, c -> o, c -> b, c -> sf where
--     -- runComponent :: OpB t (b i ': c b i o) (Tuple (b o ': If sf c b i o))
--     runComponent :: OpB t (b i ': c b i o) (Tuple (b o ': If sf '[c b i o] '[]))
--     -- data CParams c b i o :: Type
--     -- data CState  c b i o :: Type
--     -- type CState  c b i o :: Maybe Type
--     -- runComponent
--     --     :: OpB t (b i ': c b i o ': MaybeToList (CState c b i o))
--     --              (Tuple (b o ': MaybeToList (CState c b i o)))
--     -- initComponent
--     --     :: ContGen d
--     --     => Sing i
--     --     -> Sing o
--     --     -> d
--     --     -> Gen (PrimState m)
--     --     -> m (c b i o, Option I (CState c b i o))

-- data NetComponent :: (BShape Nat -> Type) -> Maybe Type -> BShape Nat -> BShape Nat -> Type where
--     NCPure
--         :: (Component c b i o, CState c b i o ~ 'Nothing, Num (c b i o))
--         => c b i o
--         -> NetComponent b 'Nothing i o
--     NCStateful
--         :: (Component c b i o, CState c b i o ~ 'Just st, Num (c b i o), Num st)
--         => c b i o
--         -> st
--         -> NetComponent b ('Just st) i o

-- -- runNetComponent
-- --     :: NetComponent st b i o
-- --     -> b i
-- --     -> (b o, NetComponent st b i o)
-- -- runNetComponent = \case
-- --     n@(NCPure p)   -> \x -> (, n) . getI . head' $ evalBPOp runComponent (x ::< p ::< Ø)
-- --     NCStateful p s -> \x -> case evalBPOp runComponent (x ::< p ::< s ::< Ø) of
-- --       I y :< I s' :< Ø -> (y, NCStateful p s')

-- -- netComponentOp
-- --     :: forall s b st i o. (Num (b i), Num (b o))
-- --     => BPOp s '[ b i, NetComponent b st i o ] '[b o, NetComponent b st i o]
-- -- netComponentOp = withInps $ \(x :< c :< Ø) ->
-- --     withGADT c $ \case
-- --       c'@(NCPure p) -> BPC (p ::< Ø) (NCPure . getI . head') $ \(pVar :< Ø) -> do
-- --         y :< Ø <- runComponent ~$$ (x :< pVar :< Ø)
-- --         return $ y :< constVar c' :< Ø
-- --       NCStateful p s -> BPC (p ::< s ::< Ø)
-- --                             (\(I gP :< I gS :< Ø) -> NCStateful gP gS)
-- --                             $ \(pVar :< sVar :< Ø) -> do
-- --         y :< sVar' :< Ø <- runComponent ~$$ (x :< pVar :< sVar :< Ø)
-- --         return $ y :< _ :< Ø
-- --         -- c' :< Ø <- isoVar (iso (\(I p' :< I s' :< Ø) -> only_ (NCStateful p' s'))
-- --         --                        (\case I (NCStateful p' s') :< Ø -> p' ::< s' ::< Ø)
-- --         --                   )
-- --         -- (c' :: BVar s '[ b i, NetComponent b st i o ] (NetComponent b st i o)) :< Ø
-- --         --     <- _
-- --             -- <- isoVar (undefined) (pVar :< sVar' :< Ø)
-- --             -- <- isoVar (iso (\(I p' :< I s' :< Ø) -> only_ (NCStateful p' s')) _)
-- --             --           (pVar :< sVar' :< Ø)
-- --         -- return $ y :< _ :< Ø
-- --       --   y :< s' :< Ø <- runComponent ~$$ (x :< p' :< Ø)


-- -- instance Every Num as => Num (Tuple as) where

-- -- netComponentOp = OpM $ \(I x :< I c :< Ø) ->
-- --     case c of
-- --       n@(NCPure p) -> do
-- --         (I y :< Ø, gF) <- runOpM' runComponent (x ::< p ::< Ø)
-- --         let out = y ::< n ::< Ø
-- --             gF' = fmap (\case I y' :< I p' :< Ø -> y' ::< NCPure p' ::< Ø)
-- --                 . gF
-- --                 . fmap (\case x' :< _ :< Ø -> x' :< Ø)
-- --         return (out, gF')
-- --       NCStateful p s -> do
-- --         (I y :< I s' :< Ø, gF) <- runOpM' runComponent (x ::< p ::< s ::< Ø)
-- --         let out = y ::< NCStateful p s' ::< Ø
-- --             gF' = fmap (\case I y' :< I p' :< I s'' :< Ø -> y' ::< NCStateful p' s'' ::< Ø)
-- --                 . gF
-- --                 . fmap (\case x' :< I (NCStateful _ s'') :< Ø -> x' :< I s'' :< Ø)
-- --         return (out, gF')

-- netComponentOp
--     :: forall s b st i o. Num (b i)
--     => OpB s '[ b i, NetComponent b st i o ] (Tuple '[b o, NetComponent b st i o])
-- netComponentOp = OpM $ \(I x :< I c :< Ø) ->
--     case c of
--       n@(NCPure p) -> do
--         (I y :< Ø, gF) <- runOpM' runComponent (x ::< p ::< Ø)
--         let out = y ::< n ::< Ø
--             gF' = fmap (\case I y' :< I p' :< Ø -> y' ::< NCPure p' ::< Ø)
--                 . gF
--                 . fmap (\case x' :< _ :< Ø -> x' :< Ø)
--         return (out, gF')
--       NCStateful p s -> do
--         (I y :< I s' :< Ø, gF) <- runOpM' runComponent (x ::< p ::< s ::< Ø)
--         let out = y ::< NCStateful p s' ::< Ø
--             gF' = fmap (\case I y' :< I p' :< I s'' :< Ø -> y' ::< NCStateful p' s'' ::< Ø)
--                 . gF
--                 . fmap (\case x' :< I (NCStateful _ s'') :< Ø -> x' :< I s'' :< Ø)
--         return (out, gF')

-- -- data Network :: NetState -> (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type where
-- --     NetExt :: NetComponent st b i o -> Network st b i o
-- --     (:&)   :: NetComponent st b i h -> Network st b h o -> Network s b i o

-- -- runNetwork
-- --     :: Network st b i o
-- --     -> b i
-- --     -> (b o, Network st b i o)
-- -- runNetwork = \case
-- --     NetExt c -> second NetExt . runNetComponent c
-- --     c :& n   -> \x -> case runNetComponent c x of
-- --       (y, c') -> case runNetwork n y of
-- --         (z, n') -> (z, c' :& n')


