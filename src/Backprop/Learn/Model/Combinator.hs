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
  , forkModel, feedback, feedbackTrace
  ) where

import           Backprop.Learn.Model.Types
import           Control.Applicative
import           Control.Category
import           Control.Monad
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Singletons
import           Data.Singletons.Prelude.List
import           Data.Singletons.Prelude.Maybe
import           Data.Type.Functor.Product
import           Data.Type.List.Sublist
import           Data.Type.Mayb                as Mayb
import           Data.Type.Tuple
import           Data.Vinyl
import           GHC.TypeNats
import           Numeric.Backprop
import           Prelude hiding                ((.), id)
import qualified Data.Vector.Sized             as SV

-- | Compose two 'Model's one after the other.
(<~)
    :: forall p q s t a b c.
     ( PureProd Maybe p
     , PureProd Maybe q
     , PureProd Maybe s
     , PureProd Maybe t
     , AllConstrainedProd Backprop p
     , AllConstrainedProd Backprop q
     , AllConstrainedProd Backprop s
     , AllConstrainedProd Backprop t
     )
    => Model  p         s        b c
    -> Model        q         t  a b
    -> Model (p :#? q) (s :#? t) a c
(<~) = withModelFunc2 $ \f g (p :#? q) x (s :#? t) -> do
    (y, t') <- g q x t
    (z, s') <- f p y s
    pure (z, s' :#? t')
infixr 8 <~

-- | Compose two 'Model's one after the other, in reverse composition order
(~>)
    :: forall p q s t a b c.
     ( PureProd Maybe p
     , PureProd Maybe q
     , PureProd Maybe s
     , PureProd Maybe t
     , AllConstrainedProd Backprop p
     , AllConstrainedProd Backprop q
     , AllConstrainedProd Backprop s
     , AllConstrainedProd Backprop t
     )
    => Model  p         s        a b
    -> Model        q         t  b c
    -> Model (p :#? q) (s :#? t) a c
(~>) = withModelFunc2 $ \f g (p :#? q) x (s :#? t) -> do
    (y, s') <- f p x s
    (z, t') <- g q y t
    pure (z, s' :#? t')
infixr 8 ~>


-- | 'Model' where parameters and states are heterogeneous lists ('T'),
-- making for more seamless composition.
type LModel ps ss a b = Model ('Just (T ps)) ('Just (T ss)) a b

-- | 'Cons' a model to the end of a chain of 'LModel' compositions.  Can be
-- used with 'nilLM'.
--
(#:)
    :: forall p ps s ss a b c.
     ( AllConstrainedProd Backprop p
     , AllConstrainedProd Backprop s
     , ReifyConstraint Backprop TF ps
     , ReifyConstraint Backprop TF ss
     , RMap ss
     , RApply ss
     , RMap ps
     , RApply ps
     )
    => Model         p                           s        b c
    -> LModel                   ps                    ss  a b
    -> LModel (MaybeToList p ++ ps) (MaybeToList s ++ ss) a c
(#:) = withModelFunc2 $ \f fs (PJust pps) x (PJust sss) -> do
    let (p, ps) = case singProd (sing @p) of
          PNothing   -> (PNothing, pps)
          PJust _ -> (PJust (pps ^^. tHead), pps ^^. tTail)
        (s, ss) = case singProd (sing @s) of
          PNothing   -> (PNothing, sss)
          PJust _ -> (PJust (sss ^^. tHead), sss ^^. tTail)
    (y, ss') <- fs (PJust ps) x (PJust ss)
    (z, s' ) <- f         p   y     s
    let sss' = case s' of
          PNothing  -> fromPJust ss'
          PJust s'J -> isoVar2 (:&&) (\case t :&& ts -> (t, ts))
                         s'J
                         (fromPJust ss')
    pure $ (z, PJust sss')
infixr 5 #:

-- | Compose two 'LModel's
(#++)
    :: forall ps qs ss ts a b c.
     ( Learnables ps
     , Learnables qs
     , Learnables ss
     , Learnables ts
     , Learnables (ps ++ qs)
     , Learnables (ss ++ ts)
     ) 
    => LModel  ps         ss        b c
    -> LModel        qs         ts  a b
    -> LModel (ps ++ qs) (ss ++ ts) a c
(#++) = withModelFunc2 $ \f g (PJust psqs) x (PJust ssts) ->
        withAppend (sing @ps) (sing @qs) $ \_ apsqs@AppendWit ->
        withAppend (sing @ss) (sing @ts) $ \_ assts@AppendWit -> do
    (y, ts) <- second fromPJust
           <$> g (PJust (psqs ^^. suffixLens (appendToSuffix apsqs)))
                 x
                 (PJust (ssts ^^. suffixLens (appendToSuffix assts)))
    (z, ss) <- second fromPJust
           <$> f (PJust (psqs ^^. prefixLens (appendToPrefix apsqs)))
                 y
                 (PJust (ssts ^^. prefixLens (appendToPrefix assts)))
    pure  ( z
          , PJust $ isoVar2 (appendRec assts) (splitRec assts) ss ts
    -- rappend @_ @ss @ts)
                              -- (tSplit @ss @ts known)
          )
infixr 5 #++

-- appendLength
--     :: Length as
--     -> Length bs
--     -> Length (as ++ bs)
-- appendLength LZ     = id
-- appendLength (LS l) = LS . appendLength l

-- | Identity of '#++'
nilLM :: Model ('Just (T '[])) ('Just (T '[])) a a
nilLM = id

-- | Lift a normal 'Model' to a 'LModel' with a singleton list
-- parameter/state if ''Just', or an empty list if ''Nothing'.  Essentially
-- prepares a model to be used with '#~' and 'nilLM'.
liftLM
    :: forall p s a b.
     ( SingI p
     , AllConstrainedProd Backprop p
     , SingI s
     , AllConstrainedProd Backprop s
     )
    => Model p s a b
    -> LModel (MaybeToList p) (MaybeToList s) a b
liftLM = withModelFunc $ \f (PJust ps) x ssM@(PJust ss) ->
    case singProd (sing @p) of
      PNothing -> case singProd (sing @s) of
        PNothing -> (fmap . second . const) ssM
            $ f PNothing x PNothing
        PJust _ -> (fmap . second) (PJust . isoVar onlyT tOnly . fromPJust)
              $ f PNothing x (PJust (isoVar tOnly onlyT ss))
      PJust _ ->
        let p = isoVar tOnly onlyT ps
        in  case singProd (sing @s) of
              PNothing -> (fmap . second . const) ssM
                  $ f (PJust p) x PNothing
              PJust _ -> (fmap . second) (PJust . isoVar onlyT tOnly . fromPJust)
                    $ f (PJust p) x (PJust (isoVar tOnly onlyT ss))

-- | Return a model that loops a model ("feed") repeatedly onto itself,
-- with a model to provide the back loop.
feedback
    :: forall p q s t a b.
     ( PureProd Maybe p
     , PureProd Maybe q
     , PureProd Maybe s
     , PureProd Maybe t
     , AllConstrainedProd Backprop p
     , AllConstrainedProd Backprop q
     , AllConstrainedProd Backprop s
     , AllConstrainedProd Backprop t
     )
    => Int                                -- ^ times
    -> Model  p         s        a b      -- ^ feed
    -> Model        q         t  b a      -- ^ back
    -> Model (p :#? q) (s :#? t) a b
feedback n = withModelFunc2 $ \feed back (p :#? q) x0 (s0 :#? t0) ->
    let go !i !x !s !t = do
            (y, s') <- feed p x s
            if i >= n
              then pure (y, (s', t))
              else do
                (z, t') <- back q y t
                go (i + 1) z s' t'
    in  second (uncurry (:#?)) <$> go 1 x0 s0 t0

-- | 'feedback', but tracing and observing all of the intermediate values.
feedbackTrace
    :: forall n p q s t a b.
     ( PureProd Maybe p
     , PureProd Maybe q
     , PureProd Maybe s
     , PureProd Maybe t
     , AllConstrainedProd Backprop p
     , AllConstrainedProd Backprop q
     , AllConstrainedProd Backprop s
     , AllConstrainedProd Backprop t
     , KnownNat n
     , Backprop b
     )
    => Model  p         s        a b      -- ^ feed
    -> Model        q         t  b a      -- ^ back
    -> Model (p :#? q) (s :#? t) a (ABP (SV.Vector n) b)
feedbackTrace = withModelFunc2 $ \feed back (p :#? q) x0 (s0 :#? t0) ->
    let go !x (!s, !t) = do
          (y, s') <- feed p x s
          (z, t') <- back q y t
          pure (y, (z, (s', t')))
    in  second (uncurry (:#?) . snd) <$>
          runStateT (collectVar . ABP <$> SV.replicateM (StateT (uncurry go)))
                   (x0, (s0, t0))

forkModel
    :: forall p q s t a b c.
     ( PureProd Maybe p
     , PureProd Maybe q
     , PureProd Maybe s
     , PureProd Maybe t
     , AllConstrainedProd Backprop p
     , AllConstrainedProd Backprop q
     , AllConstrainedProd Backprop s
     , AllConstrainedProd Backprop t
     , Backprop b
     , Backprop c
     )
    => Model  p         s        a b      -- ^ fork 1
    -> Model        q         t  a c      -- ^ fork 2
    -> Model (p :#? q) (s :#? t) a (b :# c)
forkModel = withModelFunc2 $ \f g (p :#? q) x (s0 :#? t0) -> do
    (y, s1) <- f p x s0
    (z, t1) <- g q x t0
    pure $ (y :## z, s1 :#? t1)
