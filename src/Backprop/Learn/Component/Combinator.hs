{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module Backprop.Learn.Component.Combinator (
    Chain(..)
  , (~++)
  , chainParamLength
  , chainStateLength
  ) where

import           Backprop.Learn.Class
import           Control.Monad
import           Control.Monad.Primitive
import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Equality
import           Data.Type.Length
import           Data.Type.Mayb          as Mayb
import           Data.Type.NonEmpty
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List        as List
import qualified System.Random.MWC       as MWC

-- | Chain components linearly, retaining the ability to deconstruct at
-- a later time.
data Chain :: [Type] -> [Type] -> [Type] -> Type -> Type -> Type where
    CNil  :: Chain '[] '[] '[] a a
    (:~>) :: (Learn a b l, KnownMayb (LParamMaybe l), KnownMayb (LStateMaybe l))
          => l
          -> Chain ls        ps ss b c
          -> Chain (l ': ls) (MaybeToList (LParamMaybe l) ++ ps)
                             (MaybeToList (LStateMaybe l) ++ ss)
                             a c
infixr 5 :~>

instance ( ListC (Num List.<$> ps), ListC (Num List.<$> ss) )
      => Learn a b (Chain ls ps ss a b) where
    type LParamMaybe (Chain ls ps ss a b) = NETup Mayb.<$> ToNonEmpty ps
    type LStateMaybe (Chain ls ps ss a b) = NETup Mayb.<$> ToNonEmpty ss

    initParam     = initChainParam
    initState     = initChainState
    runLearn      = runChainLearn
    runLearnStoch = runChainLearnStoch


initChainParam
    :: forall ls ps ss a b m. PrimMonad m
    => Chain ls ps ss a b
    -> MWC.Gen (PrimState m)
    -> Mayb m (NETup Mayb.<$> ToNonEmpty ps)
initChainParam = \case
    CNil -> \_ -> N_
    (l :: l) :~> ls -> case knownMayb @(LParamMaybe l) of
      N_   -> initChainParam ls
      J_ _ -> \g -> J_ $ do
        q <- fromJ_ $ initParam l g
        case chainParamLength ls of
          LZ   -> pure $ NET q TNil
          LS _ -> NET q . netT <$> fromJ_ (initChainParam ls g)

initChainState
    :: forall ls ps ss a b m. PrimMonad m
    => Chain ls ps ss a b
    -> MWC.Gen (PrimState m)
    -> Mayb m (NETup Mayb.<$> ToNonEmpty ss)
initChainState = \case
    CNil -> \_ -> N_
    (l :: l) :~> ls -> case knownMayb @(LStateMaybe l) of
      N_   -> initChainState ls
      J_ _ -> \g -> J_ $ do
        q <- fromJ_ $ initState l g
        case chainStateLength ls of
          LZ   -> pure $ NET q TNil
          LS _ -> NET q . netT <$> fromJ_ (initChainState ls g)

runChainLearn
    :: (Reifies s W, ListC (Num List.<$> ps), ListC (Num List.<$> ss))
    => Chain ls ps ss a b
    -> Mayb (BVar s) (NETup Mayb.<$> ToNonEmpty ps)
    -> BVar s a
    -> Mayb (BVar s) (NETup Mayb.<$> ToNonEmpty ss)
    -> (BVar s b, Mayb (BVar s) (NETup Mayb.<$> ToNonEmpty ss))
runChainLearn = \case
  CNil -> \_ x _ -> (x, N_)
  (l :: l) :~> ls ->
    let lenPs = chainParamLength ls
        lenSs = chainStateLength ls
    in case knownMayb @(LParamMaybe l) of
      N_ -> \ps x -> case knownMayb @(LStateMaybe l) of
        N_ -> \ss -> flip (runChainLearn ls ps) ss
                   . runLearnStateless l N_
                   $ x
        J_ _ -> case lenSs of
          LZ -> \case
            J_ (isoVar (tOnly . netT) (tNet . onlyT)->s) ->
              let (y, J_ s') = runLearn      l  N_ x (J_ s)
                  (z, _    ) = runChainLearn ls ps y N_
              in  (z, J_ $ isoVar (tNet . onlyT) (tOnly . netT) s')
          LS _ -> \case
            J_ ss -> lenSs //
              let (y, J_ s' ) = runLearn      l  N_ x (J_ (ss ^^. netHead))
                  ssTail      = isoVar tNet netT $ ss ^^. netTail
                  (z, J_ ss') = runChainLearn ls ps y (J_ ssTail)
              in  (z, J_ $ isoVar2 NET unNet s' $ isoVar netT tNet ss')
      J_ _ -> case lenPs of
        LZ -> \case
          J_ (isoVar (tOnly . netT) (tNet . onlyT)->p) -> \x -> case knownMayb @(LStateMaybe l) of
            N_ -> \ss -> flip (runChainLearn ls N_) ss
                       . runLearnStateless l (J_ p)
                       $ x
            J_ _ -> case lenSs of
              LZ -> \case
                J_ (isoVar (tOnly . netT) (tNet . onlyT)->s) ->
                  let (y, J_ s') = runLearn      l  (J_ p)  x (J_ s)
                      (z, _    ) = runChainLearn ls N_      y N_
                  in  (z, J_ $ isoVar (tNet . onlyT) (tOnly . netT) s')
              LS _ -> \case
                J_ ss -> lenSs //
                  let (y, J_ s' ) = runLearn      l  (J_ p) x (J_ (ss ^^. netHead))
                      ssTail      = isoVar tNet netT $ ss ^^. netTail
                      (z, J_ ss') = runChainLearn ls N_     y (J_ ssTail)
                  in  (z, J_ $ isoVar2 NET unNet s' $ isoVar netT tNet ss')
        LS _ -> \case
          J_ ps -> \x -> lenPs //
            let psHead = ps ^^. netHead
                psTail = isoVar tNet netT $ ps ^^. netTail
            in  case knownMayb @(LStateMaybe l) of
                  N_ -> \ss -> flip (runChainLearn ls (J_ psTail)) ss
                             . runLearnStateless l (J_ psHead)
                             $ x
                  J_ _ -> case lenSs of
                    LZ -> \case
                      J_ (isoVar (tOnly . netT) (tNet . onlyT)->s) ->
                        let (y, J_ s') = runLearn      l  (J_ psHead) x (J_ s)
                            (z, _    ) = runChainLearn ls (J_ psTail) y N_
                        in  (z, J_ $ isoVar (tNet . onlyT) (tOnly . netT) s')
                    LS _ -> \case
                      J_ ss -> lenSs //
                        let (y, J_ s' ) = runLearn      l  (J_ psHead) x (J_ (ss ^^. netHead))
                            ssTail      = isoVar tNet netT $ ss ^^. netTail
                            (z, J_ ss') = runChainLearn ls (J_ psTail) y (J_ ssTail)
                        in  (z, J_ $ isoVar2 NET unNet s' $ isoVar netT tNet ss')


runChainLearnStoch
    :: (Reifies s W, ListC (Num List.<$> ps), ListC (Num List.<$> ss), PrimMonad m)
    => Chain ls ps ss a b
    -> MWC.Gen (PrimState m)
    -> Mayb (BVar s) (NETup Mayb.<$> ToNonEmpty ps)
    -> BVar s a
    -> Mayb (BVar s) (NETup Mayb.<$> ToNonEmpty ss)
    -> m (BVar s b, Mayb (BVar s) (NETup Mayb.<$> ToNonEmpty ss))
runChainLearnStoch = \case
  CNil -> \_ _ x _ -> pure (x, N_)
  (l :: l) :~> ls -> \g ->
    let lenPs = chainParamLength ls
        lenSs = chainStateLength ls
    in case knownMayb @(LParamMaybe l) of
      N_ -> \ps x -> case knownMayb @(LStateMaybe l) of
        N_ -> \ss -> flip (runChainLearnStoch ls g ps) ss
                 <=< runLearnStochStateless l g N_
                   $ x
        J_ _ -> case lenSs of
          LZ -> \case
            J_ (isoVar (tOnly . netT) (tNet . onlyT)->s) -> do
              (y, s') <- second fromJ_
                     <$> runLearnStoch      l  g N_ x (J_ s)
              (z, _ ) <- runChainLearnStoch ls g ps y N_
              pure (z, J_ $ isoVar (tNet . onlyT) (tOnly . netT) s')
          LS _ -> \case
            J_ ss -> lenSs // do
              (y, s' ) <- second fromJ_
                      <$> runLearnStoch      l  g N_ x (J_ (ss ^^. netHead))
              let ssTail = isoVar tNet netT $ ss ^^. netTail
              (z, ss') <- second fromJ_
                      <$> runChainLearnStoch ls g ps y (J_ ssTail)
              pure  (z, J_ $ isoVar2 NET unNet s' $ isoVar netT tNet ss')
      J_ _ -> case lenPs of
        LZ -> \case
          J_ (isoVar (tOnly . netT) (tNet . onlyT)->p) -> \x -> case knownMayb @(LStateMaybe l) of
            N_ -> \ss -> flip (runChainLearnStoch ls g N_) ss
                     <=< runLearnStochStateless l g (J_ p)
                       $ x
            J_ _ -> case lenSs of
              LZ -> \case
                J_ (isoVar (tOnly . netT) (tNet . onlyT)->s) -> do
                  (y, s') <- second fromJ_
                         <$> runLearnStoch      l  g (J_ p)  x (J_ s)
                  (z, _ ) <- runChainLearnStoch ls g N_      y N_
                  pure (z, J_ $ isoVar (tNet . onlyT) (tOnly . netT) s')
              LS _ -> \case
                J_ ss -> lenSs // do
                  (y, s' ) <- second fromJ_
                          <$> runLearnStoch      l  g (J_ p) x (J_ (ss ^^. netHead))
                  let ssTail = isoVar tNet netT $ ss ^^. netTail
                  (z, ss') <- second fromJ_
                          <$> runChainLearnStoch ls g N_     y (J_ ssTail)
                  pure (z, J_ $ isoVar2 NET unNet s' $ isoVar netT tNet ss')
        LS _ -> \case
          J_ ps -> \x -> lenPs //
            let psHead = ps ^^. netHead
                psTail = isoVar tNet netT $ ps ^^. netTail
            in  case knownMayb @(LStateMaybe l) of
                  N_ -> \ss -> flip (runChainLearnStoch ls g (J_ psTail)) ss
                           <=< runLearnStochStateless l g (J_ psHead)
                             $ x
                  J_ _ -> case lenSs of
                    LZ -> \case
                      J_ (isoVar (tOnly . netT) (tNet . onlyT)->s) -> do
                        (y, s') <- second fromJ_
                               <$> runLearnStoch      l  g (J_ psHead) x (J_ s)
                        (z, _ ) <- runChainLearnStoch ls g (J_ psTail) y N_
                        pure (z, J_ $ isoVar (tNet . onlyT) (tOnly . netT) s')
                    LS _ -> \case
                      J_ ss -> lenSs // do
                        (y, s' ) <- second fromJ_
                                <$> runLearnStoch      l  g (J_ psHead) x (J_ (ss ^^. netHead))
                        let ssTail = isoVar tNet netT $ ss ^^. netTail
                        (z, ss') <- second fromJ_
                                <$> runChainLearnStoch ls g (J_ psTail) y (J_ ssTail)
                        pure (z, J_ $ isoVar2 NET unNet s' $ isoVar netT tNet ss')

-- | Appending 'Chain'
(~++)
    :: forall ls ms ps qs ss ts a b c. ()
    => Chain ls ps ss a b
    -> Chain ms qs ts b c
    -> Chain (ls ++ ms) (ps ++ qs) (ss ++ ts) a c
(~++) = \case
    CNil     -> id
    (l :: l) :~> (ls :: Chain ls' ps' ss' a' b) ->
      case assocMaybAppend @(LParamMaybe l) @ps' @qs known of
        Refl -> case assocMaybAppend @(LStateMaybe l) @ss' @ts known of
          Refl -> \ms -> (l :~> (ls ~++ ms))
            \\ appendLength (chainParamLength ls) (chainParamLength ms)
            \\ appendLength (chainStateLength ls) (chainStateLength ms)

chainParamLength
    :: Chain ls ps ss a b
    -> Length ps
chainParamLength = \case
    CNil -> LZ
    (_ :: l) :~> ls -> case knownMayb @(LParamMaybe l) of
      N_   -> chainParamLength ls
      J_ _ -> LS $ chainParamLength ls

chainStateLength
    :: Chain ls ps ss a b
    -> Length ss
chainStateLength = \case
    CNil -> LZ
    (_ :: l) :~> ls -> case knownMayb @(LStateMaybe l) of
      N_   -> chainStateLength ls
      J_ _ -> LS $ chainStateLength ls


appendLength
    :: forall as bs. ()
    => Length as
    -> Length bs
    -> Length (as ++ bs)
appendLength LZ     = id
appendLength (LS l) = LS . appendLength l

assocMaybAppend
    :: forall a bs cs. ()
    => Mayb P a
    -> (MaybeToList a ++ (bs ++ cs)) :~: ((MaybeToList a ++ bs) ++ cs)
assocMaybAppend = \case
    N_   -> Refl
    J_ _ -> Refl

---- | Data type representing trainable models.
----
---- Useful for performant composition, but you lose the ability to decompose
---- parts.
--data LearnFunc :: Type -> Type -> Type -> Type where
--    LF :: { _lfInitParam :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m p
--          , _lfRunFixed  :: forall s. Reifies s W => BVar s p -> BVar s a -> BVar s b
--          , _lfRunStoch
--                :: forall m s. (PrimMonad m, Reifies s W)
--                => MWC.Gen (PrimState m)
--                -> BVar s p
--                -> BVar s a
--                -> m (BVar s b)
--          }
--       -> LearnFunc p a b

