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

-- import           Type.Family.List
-- import           Type.Family.Maybe
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
import           Statistics.Distribution
import           System.Random.MWC
import           Type.Family.Bool

type family MaybeToList (a :: Maybe k) = (b :: [k]) | b -> a where
    MaybeToList ('Just a ) = '[a]
    MaybeToList 'Nothing   = '[]

type family ListToMaybe (a :: [k]) = (b :: Maybe k) where
    ListToMaybe (a ': as) = 'Just a
    ListToMaybe '[]       = 'Nothing

class Component c where
    type CParam c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) = (p :: Type      ) | p -> c
    type CState c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) = (s :: Maybe Type) | s -> c

    runComponent
        :: forall s b i o. ()
        => OpB s (b i ': CParam c b i o ': MaybeToList (CState c b i o))
                 (b o ': MaybeToList (CState c b i o))
    initComponent
        :: ContGen d
        => Sing i
        -> Sing o
        -> d
        -> Gen (PrimState m)
        -> m (Tuple (CParam c b i o ': MaybeToList (CState c b i o)))

data HasState :: Maybe Type -> Type where
    HSPure  :: HasState 'Nothing
    HSState :: Num a => HasState ('Just a)

data Layer :: Type -> (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type where
    LPure  :: (CState c b i o ~ 'Nothing) => CParam c b i o -> Layer c b i o
    LState :: (CState c b i o ~ 'Just s ) => CParam c b i o -> s -> Layer c b i o

instance Num (Layer c b i o)

layerIso
    :: forall c b i o. Component c
    => HasState (CState c b i o)
    -> Iso' (Layer c b i o) (Tuple (CParam c b i o ': MaybeToList (CState c b i o)))
layerIso = \case
    HSPure  -> iso (\case LPure p -> only_ p) (\case I p :< Ø -> LPure p)
    HSState -> iso (\case LState p s      -> p ::< s ::< Ø)
                   (\case I p :< I s :< Ø -> LState p s   )

layerOp
    :: forall s c b i o. (Component c, Num (CParam c b i o), Num (b o))
    => HasState (CState c b i o)
    -> BPOp s '[ b i, Layer c b i o ] '[ b o, Layer c b i o ]
layerOp = \case
    HSPure  -> withInps $ \(x :< l :< Ø) -> do
      p :< Ø <- layerIso HSPure #<~ l
      y      <- runComponent ~$ (x :< p :< Ø)
      return $ y :< l :< Ø
    HSState -> withInps $ \(x :< l :< Ø) -> do
      p :< s  :< Ø <- layerIso @c @b @i @o HSState #<~ l
      y :< s' :< Ø <- runComponent @c @s @b @i @o ~$$ (x :< p :< s :< Ø)
      l'      :< Ø <- isoVar (from (layerIso HSState) . tup1) (p :< s' :< Ø)
      return $ y :< l' :< Ø

data LChain :: Type where
    (:~) :: BShape Nat -> Type -> LChain

data NetStruct :: [LChain] -> Type where
    NSExt :: NetStruct '[]
    NSInt :: Sing n -> NetStruct hs -> NetStruct ((n ':~ c) ': hs)

data Network :: (BShape Nat -> Type) -> LChain -> [LChain] -> BShape Nat -> Type where
    NetExt :: Layer c b i o
           -> Network b (i ':~ c) '[] o
    (:&)   :: Layer c b i h
           -> Network b (h ':~ d) hs               o
           -> Network b (i ':~ c) ((h ':~ d) ': hs) o

netExt :: Iso' (Network b (i ':~ c) '[] o) (Layer c b i o)
netExt = iso (\case NetExt l -> l) NetExt

netInt :: Iso' (Network b (i ':~ c) ((h ':~ d) ': hs) o)
               (Tuple '[Layer c b i h, Network b (h ':~ d) hs o])
netInt = iso (\case l :& n          -> l ::< n ::< Ø)
             (\case I l :< I n :< Ø -> l :& n       )

instance Num (Network b i hs o)

networkOp
    :: (Num (b o), Num (CParam c b i o), Num (b i), Component c)
    => NetStruct hs
    -> BPOp s '[ b i, Network b (i ':~ c) hs o ] '[ b o, Network b (i ':~ c) hs o ]
networkOp = \case
    NSExt -> withInps $ \(x :< n :< Ø) -> do
      l :< Ø       <- (netExt . tup1) #<~ n
      y :< l' :< Ø <- layerOp _ -$$ (x :< l :< Ø)
      n' :< Ø      <- isoVar (from tup1 . from netExt . tup1) (l' :< Ø)
      return $ y :< n' :< Ø


-- (i ~: C) [j ~: C, k ~: C] o

-- -- net i c1 h1 c2 h2 c3 o

-- -- Net (i ~: C :~ h1 ~: C :~ h2 ~: C) o


-- lPure :: Iso' (Layer c b i o) (CParam c b i o)
-- lPure = iso _ _

-- data Layer c b i o where
--     LPure :: CParam c b i o

-- type family IsJust (a :: Maybe k) = (b :: Bool) where
--     IsJust ('Just a) = 'True
--     IsJust 'Nothing  = 'False

-- data Statefulness = Stateful
--                   | NonStateful

-- class Component (c :: (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type) where
--     type CState c (b :: BShape Nat -> Type) (i :: BShape Nat) (o :: BShape Nat) :: Maybe Type
--     runComponent
--         :: OpB t (b i ': c b i o ': MaybeToList (CState c b i o))
--                  (b o ': MaybeToList (CState c b i o))
--     initComponent
--         :: ContGen d
--         => Sing i
--         -> Sing o
--         -> d
--         -> Gen (PrimState m)
--         -> m (c b i o, Option I (CState c b i o))

-- data Params
--         :: Statefulness
--         -> ((BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type)
--         -> (BShape Nat -> Type)
--         -> BShape Nat
--         -> BShape Nat
--         -> Type where
--     PPure
--         :: (Num (c b i o), Component c, CState c b i o ~ 'Nothing)
--         => c b i o
--         -> Params s c b i o
--     PStateful
--         :: (Num (c b i o), Num st, Component c, CState c b i o ~ 'Just st)
--         => c b i o
--         -> st
--         -> Params Stateful c b i o

-- instance Component c => Num (Params s c b i o) where
--     (+) = \case
--       PPure x -> \case
--         PPure y -> PPure (x + y)
--       PStateful x s -> \case
--         PStateful y t -> PStateful (x + y) (s + t)

-- pPure
--     :: (CState c b i o ~ 'Nothing, Num (c b i o), Component c)
--     => Iso' (Params s c b i o) (c b i o)
-- pPure = iso (\case PPure p -> p) PPure

-- pStateful
--     :: (CState c b i o ~ 'Just st, Num (c b i o), Num st, Component c)
--     => Iso' (Params Stateful c b i o) (Tuple '[c b i o, st])
-- pStateful = iso (\case PStateful p s   -> p ::< s ::< Ø)
--                 (\case I p :< I s :< Ø -> PStateful p s)

-- paramsOpPure
--     :: forall s sf c b i o.
--      ( Num (b o)
--      , CState c b i o ~ 'Nothing
--      , Component c
--      , Num (c b i o)
--      )
--     => BPOp s '[ b i, Params sf c b i o ] '[ b o ]
-- paramsOpPure = withInps $ \(x :< p :< Ø) -> do
--     c <- opIso pPure ~$ (p :< Ø)
--     y <- runComponent ~$ (x :< c :< Ø)
--     return $ only y

-- paramsOp
--     :: forall s sf c b i o. Num (b o)
--     => BPOp s '[ b i, Params sf c b i o ] '[ b o, Params sf c b i o ]
-- paramsOp = withInps $ \(x :< c :< Ø) ->
--     withGADT c $ \case
--       PPure p -> BPC (only_ p) (PPure . getI . head') $ \(pVar :< Ø) -> do
--         y <- runComponent ~$ (x :< pVar :< Ø)
--         c' <- opIso (from pPure) ~$ (pVar :< Ø)
--         return $ y :< c' :< Ø
--       PStateful p (s :: st) -> BPC (p ::< s ::< Ø)
--                                    (\case I p' :< I s' :< Ø -> PStateful p' s')
--                                       $ \(pVar :< sVar :< Ø) -> do
--         y :< sVar' :< Ø <- runComponent ~$$ (x :< pVar :< sVar :< Ø)
--         c' :< Ø <- isoVar (from pStateful . tup1) (pVar :< sVar' :< Ø)
--         return $ y :< c' :< Ø

-- data Network
--         :: Statefulness
--         -> (BShape Nat -> Type)
--         -> (BShape Nat, ((BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type))
--         -> [(BShape Nat, (BShape Nat -> Type) -> BShape Nat -> BShape Nat -> Type)]
--         -> BShape Nat
--         -> Type
--         where
--     NetExt
--         :: Params s c b i o
--         -> Network s b '(i, c) '[] o
--     (:&)
--         :: (Num (b h), Component d)
--         => Params s c b i h
--         -> Network s b '(h, d) hs o
--         -> Network s b '(i, c) ( '(h, d) ': hs ) o

-- instance Num (Network s b i hs o)

-- netExt :: Iso' (Network s b '(i, c) '[] o) (Params s c b i o)
-- netExt = iso (\case NetExt p -> p) NetExt

-- netInt
--     :: (Num (b h), Component d)
--     => Iso' (Network s b '(i, c) ( '(h, d) ': hs ) o) (Tuple '[Params s c b i h, Network s b '(h, d) hs o])
-- netInt = iso (\case p :& n          -> p ::< n ::< Ø)
--              (\case I p :< I n :< Ø -> p :& n       )


-- networkOp
--     :: (Num (b i), Component c, Num (b o))
--     => BPOp s '[ b i, Network sf b '(i, c) hs o] '[ b o, Network sf b '(i, c) hs o ]
-- networkOp = withInps $ \(x :< n :< Ø) -> do
--     withGADT n $ \case
--       NetExt p -> BPC (only_ p) (NetExt . getI . head') $ \(pVar :< Ø) -> do
--         y :< pVar' :< Ø <- paramsOp -$$ (x :< pVar :< Ø)
--         n' <- opIso (from netExt) ~$ (pVar' :< Ø)
--         return $ y :< n' :< Ø
--       p :& n' -> BPC (p ::< n' ::< Ø) (\case I p' :< I n'' :< Ø -> p' :& n'')
--                        $ \(pVar :< nVar :< Ø) -> do
--         y :< pVar' :< Ø <- paramsOp -$$ (x :< pVar :< Ø)
--         z :< nVar' :< Ø <- networkOp -$$ (y :< nVar :< Ø)
--         newNet :< Ø <- isoVar (from netInt . tup1) (pVar' :< nVar' :< Ø)
--         return $ z :< newNet :< Ø

