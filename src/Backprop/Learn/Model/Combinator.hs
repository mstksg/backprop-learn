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
  , LModel, (#:), nilLM, (#++), liftLM
    -- * Misc
  , feedback, feedbackTrace
  ) where

import           Backprop.Learn.Model.Types
import           Control.Applicative
import           Control.Category
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Type.Length
import           Data.Type.Mayb             as Mayb
import           Data.Type.Tuple
import           GHC.TypeNats
import           Numeric.Backprop
import           Prelude hiding             ((.), id)
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List           as List
import qualified Data.Vector.Sized          as SV

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
(<~) = withModelFunc2 $ \f g (p :&? q) x (s :&? t) -> do
    (y, t') <- g q x t
    (z, s') <- f p y s
    pure (z, s' :&? t')
infixr 8 <~

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
infixr 8 ~>


-- | 'Model' where parameters and states are heterogeneous lists ('T'),
-- making for more seamless composition.
type LModel ps ss a b = Model ('Just (T ps)) ('Just (T ss)) a b

-- | 'Cons' a model to the end of a chain of 'LModel' compositions.  Can be
-- used with 'nilLM'.
--
(#:)
    :: forall p ps s ss a b c.
     ( MaybeC Backprop p
     , ListC (Backprop List.<$> ps)
     , MaybeC Backprop s
     , ListC (Backprop List.<$> ss)
     , KnownMayb p
     , KnownMayb s
     -- , ListC (Backprop List.<$> (ss ++ ts))
     -- , Known Length ps
     -- , Known Length ss
     -- , Known Length ts
     )
    => Model         p                           s        b c
    -> LModel                   ps                    ss  a b
    -> LModel (MaybeToList p ++ ps) (MaybeToList s ++ ss) a c
(#:) = withModelFunc2 $ \f fs (J_ pps) x (J_ sss) -> do
    let (p, ps) = case knownMayb @p of
          N_   -> (N_, pps)
          J_ _ -> (J_ (pps ^^. tHead), pps ^^. tTail)
        (s, ss) = case knownMayb @s of
          N_   -> (N_, sss)
          J_ _ -> (J_ (sss ^^. tHead), sss ^^. tTail)
    (y, ss') <- fs (J_ ps) x (J_ ss)
    (z, s' ) <- f      p   y     s
    let sss' = case s' of
                 N_     -> fromJ_ ss'
                 J_ s'J -> isoVar2 (:#) (\case t :# ts -> (t, ts)) s'J (fromJ_ ss')
    pure $ (z, J_ sss')
infixr 5 #:

-- | Compose two 'LModel's
(#++)
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
(#++) = withModelFunc2 $ \f g (J_ psqs) x (J_ ssts) ->
        appendLength @ss @ts known known // do
    (y, ts) <- second fromJ_
           <$> g (J_ (psqs ^^. tDrop @ps @qs known))
                 x
                 (J_ (ssts ^^. tDrop @ss @ts known))
    (z, ss) <- second fromJ_
           <$> f (J_ (psqs ^^. tTake @ps @qs known))
                 y
                 (J_ (ssts ^^. tTake @ss @ts known))
    pure  (z, J_ $ isoVar2 (tAppend @ss @ts) (tSplit @ss @ts known)
                           ss ts
          )
infixr 5 #++

appendLength
    :: Length as
    -> Length bs
    -> Length (as ++ bs)
appendLength LZ     = id
appendLength (LS l) = LS . appendLength l

-- | Identity of '#++'
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
liftLM = withModelFunc $ \f (J_ ps) x ssM@(J_ ss) ->
    case knownMayb @p of
      N_ -> case knownMayb @s of
        N_ -> (fmap . second . const) ssM
            $ f N_ x N_
        J_ _ -> (fmap . second) (J_ . isoVar onlyT tOnly . fromJ_)
              $ f N_ x (J_ (isoVar tOnly onlyT ss))
      J_ _ ->
        let p = isoVar tOnly onlyT ps
        in  case knownMayb @s of
              N_ -> (fmap . second . const) ssM
                  $ f (J_ p) x N_
              J_ _ -> (fmap . second) (J_ . isoVar onlyT tOnly . fromJ_)
                    $ f (J_ p) x (J_ (isoVar tOnly onlyT ss))

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
feedback n = withModelFunc2 $ \feed back (p :&? q) x0 (s0 :&? t0) ->
    let go !i !x !s !t = do
            (y, s') <- feed p x s
            if i >= n
              then pure (y, (s', t))
              else do
                (z, t') <- back q y t
                go (i + 1) z s' t'
    in  second (uncurry (:&?)) <$> go 1 x0 s0 t0

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
feedbackTrace = withModelFunc2 $ \feed back (p :&? q) x0 (s0 :&? t0) ->
    let go !x (!s, !t) = do
          (y, s') <- feed p x s
          (z, t') <- back q y t
          pure (y, (z, (s', t')))
    in  second (uncurry (:&?) . snd) <$>
          runStateT (collectVar . ABP <$> SV.replicateM (StateT (uncurry go)))
                   (x0, (s0, t0))
