{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveDataTypeable     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module Backprop.Learn.Model.Combinator (
    -- * Tuple-based Composition
    (~>), (<~)
    -- * List-based Composition
  , LModel, (#~), nilLM, liftLM
    -- * Misc
  , feedback, feedbackTrace
  ) where

import           Backprop.Learn.Model.Types
import           Control.Applicative
import           Control.Category
import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Type.Length
import           Data.Type.Mayb             as Mayb
import           Data.Type.Tuple hiding     (T2(..), T3(..))
import           GHC.TypeNats
import           Numeric.Backprop
import           Prelude hiding             ((.), id)
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List           as List
import qualified Data.Vector.Sized          as SV
import qualified System.Random.MWC          as MWC

-- | Compose two 'Model's one after the other.
(<~)
    :: forall p q s t a b c.
     ( KnownMayb p
     , KnownMayb q
     , KnownMayb s
     , KnownMayb t
     , MaybeC Backprop p
     , MaybeC Backprop q
     , MaybeC Backprop s
     , MaybeC Backprop t
     )
    => Model           p              s    b c
    -> Model             q              t  a b
    -> Model (TupMaybe p q) (TupMaybe s t) a c
f <~ g = Model
    { runLearn = \pq x st ->
        let (p, q) = splitTupMaybe @_ @p @q (\(T2B v u) -> (v, u)) pq
            (s, t) = splitTupMaybe @_ @s @t (\(T2B v u) -> (v, u)) st
            (y, t') = runLearn g q x t
            (z, s') = runLearn f p y s
        in  (z, tupMaybe T2B s' t')
    , runLearnStoch = \gen pq x st -> do
        let (p, q) = splitTupMaybe @_ @p @q (\(T2B v u) -> (v, u)) pq
            (s, t) = splitTupMaybe @_ @s @t (\(T2B v u) -> (v, u)) st
        (y, t') <- runLearnStoch g gen q x t
        (z, s') <- runLearnStoch f gen p y s
        pure (z, tupMaybe T2B s' t')
    }

-- | Compose two 'Model's one after the other, in reverse composition order
(~>)
    :: forall p q s t a b c.
     ( KnownMayb p
     , KnownMayb q
     , KnownMayb s
     , KnownMayb t
     , MaybeC Backprop p
     , MaybeC Backprop q
     , MaybeC Backprop s
     , MaybeC Backprop t
     )
    => Model             q              t  a b
    -> Model           p              s    b c
    -> Model (TupMaybe p q) (TupMaybe s t) a c
f ~> g = g <~ f


-- | 'Model' where parameters and states are heterogeneous lists ('T'),
-- making for more seamless composition.
type LModel ps ss a b = Model ('Just (T ps)) ('Just (T ss)) a b

-- | Compose two 'LModel's
(#~)
    :: forall ps qs ss ts a b c.
     ( ListC (Backprop List.<$> ps)
     , ListC (Backprop List.<$> qs)
     , ListC (Backprop List.<$> ss)
     , ListC (Backprop List.<$> ts)
     , ListC (Backprop List.<$> (ss ++ ts))
     , Known Length ps
     , Known Length ss
     , Known Length ts
     )
    => LModel  ps         ss        b c
    -> LModel        qs         ts  a b
    -> LModel (ps ++ qs) (ss ++ ts) a c
f #~ g = Model
    { runLearn  = \(J_ psqs) x (J_ ssts) -> appendLength @ss @ts known known //
        let (y, J_ ts) = runLearn g (J_ (psqs ^^. tDrop @ps @qs known))
                                    x
                                    (J_ (ssts ^^. tDrop @ss @ts known))
            (z, J_ ss) = runLearn f (J_ (psqs ^^. tTake @ps @qs known))
                                    y
                                    (J_ (ssts ^^. tTake @ss @ts known))
        in  (z, J_ $ isoVar2 (tAppend @ss @ts) (tSplit @ss @ts known)
                             ss ts
            )
    , runLearnStoch = \gen (J_ psqs) x (J_ ssts) -> appendLength @ss @ts known known // do
        (y, ts) <- second fromJ_
               <$> runLearnStoch g gen (J_ (psqs ^^. tDrop @ps @qs known))
                                       x
                                       (J_ (ssts ^^. tDrop @ss @ts known))
        (z, ss) <- second fromJ_
               <$> runLearnStoch f gen (J_ (psqs ^^. tTake @ps @qs known))
                                        y
                                        (J_ (ssts ^^. tTake @ss @ts known))
        pure  (z, J_ $ isoVar2 (tAppend @ss @ts) (tSplit @ss @ts known)
                               ss ts
              )
    }

appendLength
    :: Length as
    -> Length bs
    -> Length (as ++ bs)
appendLength LZ     = id
appendLength (LS l) = LS . appendLength l

-- | Identity of '#~'
nilLM :: Model ('Just (T '[])) ('Just (T '[])) a a
nilLM = id

-- | Lift a normal 'Model' to a 'LModel' with a singleton list
-- parameter/state if ''Just', or an empty list if ''Nothing'.  Essentially
-- prepares a model to be used with '#~' and 'nilLM'.
liftLM
    :: forall p s a b.
     ( KnownMayb p
     , MaybeC Backprop p
     , KnownMayb s
     , MaybeC Backprop s
     )
    => Model p s a b
    -> LModel (MaybeToList p) (MaybeToList s) a b
liftLM f = Model
    { runLearn = \(J_ ps) x ssM@(J_ ss) -> case knownMayb @p of
        N_ -> case knownMayb @s of
          N_ -> (second . const) ssM
              $ runLearn f N_ x N_
          J_ _ -> second (J_ . isoVar onlyT tOnly . fromJ_)
                $ runLearn f N_ x (J_ (isoVar tOnly onlyT ss))
        J_ _ ->
          let p = isoVar tOnly onlyT ps
          in  case knownMayb @s of
                N_ -> (second . const) ssM
                    $ runLearn f (J_ p) x N_
                J_ _ -> second (J_ . isoVar onlyT tOnly . fromJ_)
                      $ runLearn f (J_ p) x (J_ (isoVar tOnly onlyT ss))
    , runLearnStoch = \g (J_ ps) x ssM@(J_ ss) -> case knownMayb @p of
        N_ -> case knownMayb @s of
          N_ -> (fmap . second . const) ssM
              $ runLearnStoch f g N_ x N_
          J_ _ -> (fmap . second) (J_ . isoVar onlyT tOnly . fromJ_)
                $ runLearnStoch f g N_ x (J_ (isoVar tOnly onlyT ss))
        J_ _ ->
          let p = isoVar tOnly onlyT ps
          in  case knownMayb @s of
                N_ -> (fmap . second . const) ssM
                    $ runLearnStoch f g (J_ p) x N_
                J_ _ -> (fmap . second) (J_ . isoVar onlyT tOnly . fromJ_)
                      $ runLearnStoch f g (J_ p) x (J_ (isoVar tOnly onlyT ss))
    }

-- | Return a model that loops a model ("feed") repeatedly onto itself,
-- with a model to provide the back loop.
feedback
    :: forall p q s t a b.
     ( KnownMayb p
     , KnownMayb q
     , KnownMayb s
     , KnownMayb t
     , MaybeC Backprop p
     , MaybeC Backprop q
     , MaybeC Backprop s
     , MaybeC Backprop t
     )
    => Int                                          -- ^ times
    -> Model           p              s    a b      -- ^ feed
    -> Model             q              t  b a      -- ^ back
    -> Model (TupMaybe p q) (TupMaybe s t) a b
feedback n feed back = Model rL rLS
  where
    rL  :: forall z. (Reifies z W)
        => Mayb (BVar z) (TupMaybe p q)
        -> BVar z a
        -> Mayb (BVar z) (TupMaybe s t)
        -> (BVar z b, Mayb (BVar z) (TupMaybe s t))
    rL pq x0 st0 = second (uncurry (tupMaybe T2B)) $ go 1 x0 s0 t0
      where
        go  :: Int
            -> BVar z a
            -> Mayb (BVar z) s
            -> Mayb (BVar z) t
            -> (BVar z b, (Mayb (BVar z) s, Mayb (BVar z) t))
        go !i !x !s !t
            | i >= n    = (y, (s', t))
            | otherwise = go (i + 1) z s' t'
          where
            (y, s') = runLearn feed p x s
            (z, t') = runLearn back q y t
        (p , q ) = splitTupMaybe @_ @p @q (\(T2B v u) -> (v, u)) pq
        (s0, t0) = splitTupMaybe @_ @s @t (\(T2B v u) -> (v, u)) st0
    rLS :: forall m z. (PrimMonad m, Reifies z W)
        => MWC.Gen (PrimState m)
        -> Mayb (BVar z) (TupMaybe p q)
        -> BVar z a
        -> Mayb (BVar z) (TupMaybe s t)
        -> m (BVar z b, Mayb (BVar z) (TupMaybe s t))
    rLS g pq x0 st0 = second (uncurry (tupMaybe T2B)) <$> go 1 x0 s0 t0
      where
        go  :: Int
            -> BVar z a
            -> Mayb (BVar z) s
            -> Mayb (BVar z) t
            -> m (BVar z b, (Mayb (BVar z) s, Mayb (BVar z) t))
        go !i !x !s !t = do
            (y, s') <- runLearnStoch feed g p x s
            if i >= n
              then pure (y, (s', t))
              else do
                (z, t') <- runLearnStoch back g q y t
                go (i + 1) z s' t'
        (p , q ) = splitTupMaybe @_ @p @q (\(T2B v u) -> (v, u)) pq
        (s0, t0) = splitTupMaybe @_ @s @t (\(T2B v u) -> (v, u)) st0

-- | 'feedback', but tracing and observing all of the intermediate values.
feedbackTrace
    :: forall n p q s t a b.
     ( KnownMayb p
     , KnownMayb q
     , KnownMayb s
     , KnownMayb t
     , MaybeC Backprop p
     , MaybeC Backprop q
     , MaybeC Backprop s
     , MaybeC Backprop t
     , KnownNat n
     , Backprop b
     )
    => Model           p              s    a b      -- ^ feed
    -> Model             q              t  b a      -- ^ back
    -> Model (TupMaybe p q) (TupMaybe s t) a (ABP (SV.Vector n) b)
feedbackTrace feed back = Model rL rLS
  where
    rL  :: forall z. (Reifies z W)
        => Mayb (BVar z) (TupMaybe p q)
        -> BVar z a
        -> Mayb (BVar z) (TupMaybe s t)
        -> (BVar z (ABP (SV.Vector n) b), Mayb (BVar z) (TupMaybe s t))
    rL pq x0 st0 = second (uncurry (tupMaybe T2B) . snd) $
        runState (collectVar . ABP <$> SV.replicateM (state (uncurry go)))
                 (x0, (s0, t0))
      where
        go  :: BVar z a
            -> (Mayb (BVar z) s, Mayb (BVar z) t)
            -> (BVar z b, (BVar z a, (Mayb (BVar z) s, Mayb (BVar z) t)))
        go !x (!s, !t) = (y, (z, (s', t')))
          where
            (y, s') = runLearn feed p x s
            (z, t') = runLearn back q y t
        (p , q ) = splitTupMaybe @_ @p @q (\(T2B v u) -> (v, u)) pq
        (s0, t0) = splitTupMaybe @_ @s @t (\(T2B v u) -> (v, u)) st0
    rLS :: forall m z. (PrimMonad m, Reifies z W)
        => MWC.Gen (PrimState m)
        -> Mayb (BVar z) (TupMaybe p q)
        -> BVar z a
        -> Mayb (BVar z) (TupMaybe s t)
        -> m (BVar z (ABP (SV.Vector n) b), Mayb (BVar z) (TupMaybe s t))
    rLS g pq x0 st0 = second (uncurry (tupMaybe T2B) . snd) <$>
        runStateT (collectVar . ABP <$> SV.replicateM (StateT (uncurry go)))
                 (x0, (s0, t0))
      where
        go  :: BVar z a
            -> (Mayb (BVar z) s, Mayb (BVar z) t)
            -> m (BVar z b, (BVar z a, (Mayb (BVar z) s, Mayb (BVar z) t)))
        go !x (!s, !t) = do
          (y, s') <- runLearnStoch feed g p x s
          (z, t') <- runLearnStoch back g q y t
          pure (y, (z, (s', t')))
        (p , q ) = splitTupMaybe @_ @p @q (\(T2B v u) -> (v, u)) pq
        (s0, t0) = splitTupMaybe @_ @s @t (\(T2B v u) -> (v, u)) st0
