{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE RankNTypes             #-}
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
    Feedback(..), feedbackId
  , FeedbackTrace(..), feedbackTraceId
  , Chain(..)
  , (~++)
  , chainParamLength
  , chainStateLength
  , LearnFunc(..), learnFunc
  , LMap(..), RMap(..)
  , Dimap, pattern DM, _dmPre, _dmPost, _dmLearn
  , (.~)
  , nilLF, onlyLF
  ) where

import           Backprop.Learn.Model
import           Control.Applicative
import           Control.Category
import           Control.Monad
import           Control.Monad.Primitive
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Kind
import           Data.Type.Equality
import           Data.Type.Length
import           Data.Type.Mayb            as Mayb
import           Data.Type.NonEmpty
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Prelude hiding            ((.), id)
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List          as List
import qualified Data.Vector.Sized         as SV
import qualified System.Random.MWC         as MWC

-- | Chain components linearly, retaining the ability to deconstruct at
-- a later time.
data Chain :: [Type] -> [Type] -> [Type] -> Type -> Type -> Type where
    CNil  :: Chain '[] '[] '[] a a
    (:~>) :: (Learn a b l, KnownMayb (LParamMaybe l), KnownMayb (LStateMaybe l))
          => !l
          -> !(Chain ls        ps ss b c)
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

-- | Data type representing trainable models.
--
-- Useful for performant composition, but you lose the ability to decompose
-- parts.
data LearnFunc :: Maybe Type -> Maybe Type -> Type -> Type -> Type where
    LF :: { _lfInitParam :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m p
          , _lfInitState :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m s
          , _lfRunLearn
               :: forall q. Reifies q W
               => Mayb (BVar q) p
               -> BVar q a
               -> Mayb (BVar q) s
               -> (BVar q b, Mayb (BVar q) s)
          , _lfRunLearnStoch
               :: forall m q. (PrimMonad m, Reifies q W)
               => MWC.Gen (PrimState m)
               -> Mayb (BVar q) p
               -> BVar q a
               -> Mayb (BVar q) s
               -> m (BVar q b, Mayb (BVar q) s)
          }
       -> LearnFunc p s a b

learnFunc
    :: Learn a b l
    => l
    -> LearnFunc (LParamMaybe l) (LStateMaybe l) a b
learnFunc l = LF { _lfInitParam     = initParam l
                 , _lfInitState     = initState l
                 , _lfRunLearn      = runLearn l
                 , _lfRunLearnStoch = runLearnStoch l
                 }

instance Learn a b (LearnFunc p s a b) where
    type LParamMaybe (LearnFunc p s a b) = p
    type LStateMaybe (LearnFunc p s a b) = s

    initParam     = _lfInitParam
    initState     = _lfInitState
    runLearn      = _lfRunLearn
    runLearnStoch = _lfRunLearnStoch

instance (MaybeC Num p, MaybeC Num s, KnownMayb p, KnownMayb s) => Category (LearnFunc p s) where
    id = LF { _lfInitParam     = \_ -> map1 (pure 0 \\) $ maybeWit @_ @Num @p
            , _lfInitState     = \_ -> map1 (pure 0 \\) $ maybeWit @_ @Num @s
            , _lfRunLearn      = \_ -> (,)
            , _lfRunLearnStoch = \_ _ x -> pure . (x,)
            }
    f . g = LF { _lfInitParam = \gen -> zipMayb3 (liftA2 (+) \\)
                      (maybeWit @_ @Num @p)
                      (_lfInitParam f gen)
                      (_lfInitParam g gen)
               , _lfInitState = \gen -> zipMayb3 (liftA2 (+) \\)
                      (maybeWit @_ @Num @s)
                      (_lfInitState f gen)
                      (_lfInitState g gen)
               , _lfRunLearn  = \p x s0 ->
                    let (y, s1) = _lfRunLearn g p x s0
                    in  _lfRunLearn f p y s1
               , _lfRunLearnStoch = \gen p x s0 -> do
                    (y, s1) <- _lfRunLearnStoch g gen p x s0
                    _lfRunLearnStoch f gen p y s1
               }

-- | Compose two 'LearnFunc' on lists.
(.~)
    :: forall ps qs ss ts a b c.
     ( ListC (Num List.<$> ps)
     , ListC (Num List.<$> qs)
     , ListC (Num List.<$> ss)
     , ListC (Num List.<$> ts)
     , ListC (Num List.<$> (ss ++ ts))
     , Known Length ps
     , Known Length qs
     , Known Length ss
     , Known Length ts
     )
    => LearnFunc ('Just (T ps        )) ('Just (T ss         )) b c
    -> LearnFunc ('Just (T qs        )) ('Just (T ts         )) a b
    -> LearnFunc ('Just (T (ps ++ qs))) ('Just (T (ss ++ ts ))) a c
f .~ g = LF { _lfInitParam = \gen -> J_ $ tAppend <$> fromJ_ (_lfInitParam f gen)
                                                  <*> fromJ_ (_lfInitParam g gen)
            , _lfInitState = \gen -> J_ $ tAppend <$> fromJ_ (_lfInitState f gen)
                                                  <*> fromJ_ (_lfInitState g gen)

            , _lfRunLearn  = \(J_ psqs) x (J_ ssts) -> appendLength @ss @ts known known //
                let (y, J_ ts) = _lfRunLearn g (J_ (psqs ^^. tDrop @ps @qs known))
                                               x
                                               (J_ (ssts ^^. tDrop @ss @ts known))
                    (z, J_ ss) = _lfRunLearn f (J_ (psqs ^^. tTake @ps @qs known))
                                               y
                                               (J_ (ssts ^^. tTake @ss @ts known))
                in  (z, J_ $ isoVar2 (tAppend @ss @ts) (tSplit @ss @ts known)
                                     ss ts
                    )
            , _lfRunLearnStoch = \gen (J_ psqs) x (J_ ssts) -> appendLength @ss @ts known known // do
                (y, ts) <- second fromJ_
                       <$> _lfRunLearnStoch g gen (J_ (psqs ^^. tDrop @ps @qs known))
                                                  x
                                                  (J_ (ssts ^^. tDrop @ss @ts known))
                (z, ss) <- second fromJ_
                       <$> _lfRunLearnStoch f gen (J_ (psqs ^^. tTake @ps @qs known))
                                                   y
                                                   (J_ (ssts ^^. tTake @ss @ts known))
                pure  (z, J_ $ isoVar2 (tAppend @ss @ts) (tSplit @ss @ts known)
                                       ss ts
                      )
            }

-- | Identity of '.~'
nilLF :: LearnFunc ('Just (T '[])) ('Just (T '[])) a a
nilLF = id

-- | 'LearnFunc' with singleton lists; meant to be used with '.~'
onlyLF
    :: forall p s a b. (KnownMayb p, MaybeC Num p, KnownMayb s, MaybeC Num s)
    => LearnFunc p s a b
    -> LearnFunc ('Just (T (MaybeToList p))) ('Just (T (MaybeToList s))) a b
onlyLF f = LF
    { _lfInitParam = J_
                   . fmap prodT
                   . traverse1 (fmap I)
                   . maybToList
                   . _lfInitParam f
    , _lfInitState = J_
                   . fmap prodT
                   . traverse1 (fmap I)
                   . maybToList
                   . _lfInitState f
    , _lfRunLearn = \(J_ ps) x ssM@(J_ ss) -> case knownMayb @p of
        N_ -> case knownMayb @s of
          N_ -> (second . const) ssM
              $ _lfRunLearn f N_ x N_
          J_ _ -> second (J_ . isoVar onlyT tOnly . fromJ_)
                $ _lfRunLearn f N_ x (J_ (isoVar tOnly onlyT ss))
        J_ _ ->
          let p = isoVar tOnly onlyT ps
          in  case knownMayb @s of
                N_ -> (second . const) ssM
                    $ _lfRunLearn f (J_ p) x N_
                J_ _ -> second (J_ . isoVar onlyT tOnly . fromJ_)
                      $ _lfRunLearn f (J_ p) x (J_ (isoVar tOnly onlyT ss))
    , _lfRunLearnStoch = \g (J_ ps) x ssM@(J_ ss) -> case knownMayb @p of
        N_ -> case knownMayb @s of
          N_ -> (fmap . second . const) ssM
              $ _lfRunLearnStoch f g N_ x N_
          J_ _ -> (fmap . second) (J_ . isoVar onlyT tOnly . fromJ_)
                $ _lfRunLearnStoch f g N_ x (J_ (isoVar tOnly onlyT ss))
        J_ _ ->
          let p = isoVar tOnly onlyT ps
          in  case knownMayb @s of
                N_ -> (fmap . second . const) ssM
                    $ _lfRunLearnStoch f g (J_ p) x N_
                J_ _ -> (fmap . second) (J_ . isoVar onlyT tOnly . fromJ_)
                      $ _lfRunLearnStoch f g (J_ p) x (J_ (isoVar tOnly onlyT ss))
    }

-- | Compose two layers sequentially
data (:.~) :: Type -> Type -> Type where
    (:.~) :: !l -> !m -> l :.~ m

instance ( Learn b c l
         , Learn a b m
         , KnownMayb (LParamMaybe l)
         , KnownMayb (LParamMaybe m)
         , KnownMayb (LStateMaybe l)
         , KnownMayb (LStateMaybe m)
         , MaybeC Num (LParamMaybe l)
         , MaybeC Num (LParamMaybe m)
         , MaybeC Num (LStateMaybe l)
         , MaybeC Num (LStateMaybe m)
         )
      => Learn a c (l :.~ m) where
    type LParamMaybe (l :.~ m) = TupMaybe (LParamMaybe l) (LParamMaybe m)
    type LStateMaybe (l :.~ m) = TupMaybe (LStateMaybe l) (LStateMaybe m)

    initParam (l :.~ m) g = tupMaybe @_ @(LParamMaybe l) @(LParamMaybe m)
        (liftA2 T2)
        (initParam l g)
        (initParam m g)

    initState (l :.~ m) g = tupMaybe @_ @(LStateMaybe l) @(LStateMaybe m)
        (liftA2 T2)
        (initState l g)
        (initState m g)

    runLearn (l :.~ m) pq x st = (z, tupMaybe (isoVar2 T2 t2Tup) s' t')
      where
        (p, q) = splitTupMaybe @_ @(LParamMaybe l) @(LParamMaybe m)
                  (\v -> (v ^^. t2_1, v ^^. t2_2))
                  pq
        (s, t) = splitTupMaybe @_ @(LStateMaybe l) @(LStateMaybe m)
                  (\v -> (v ^^. t2_1, v ^^. t2_2))
                  st
        (y, t') = runLearn m q x t
        (z, s') = runLearn l p y s

    runLearnStoch (l :.~ m) g pq x st = do
        (y, t') <- runLearnStoch m g q x t
        (z, s') <- runLearnStoch l g p y s
        pure (z, tupMaybe (isoVar2 T2 t2Tup) s' t')
      where
        (p, q) = splitTupMaybe @_ @(LParamMaybe l) @(LParamMaybe m)
                  (\v -> (v ^^. t2_1, v ^^. t2_2))
                  pq
        (s, t) = splitTupMaybe @_ @(LStateMaybe l) @(LStateMaybe m)
                  (\v -> (v ^^. t2_1, v ^^. t2_2))
                  st

-- | Pre-compose a pure parameterless function to a model.
--
-- An @'LMap' b a@ takes a model from @b@ and turns it into a model from
-- @a@.
data LMap :: Type -> Type -> Type -> Type where
    LM :: { _lmPre   :: forall s. Reifies s W => BVar s a -> BVar s b
          , _lmLearn :: !l
          }
       -> LMap b a l

-- | Post-compose a pure parameterless function to a model.
--
-- An @'Rmap' b c@ takes a model returning @b@ and turns it into
-- a model returning @c@.
data RMap :: Type -> Type -> Type -> Type where
    RM :: { _rmPost  :: forall s. Reifies s W => BVar s b -> BVar s c
          , _rmLearn :: !l
          }
       -> RMap b c l

-- | Pre- and post-compose pure parameterless functions to a model.
--
-- A @'Dimap' b c a d@ takes a model from @b@ to @c@ and turns it into
-- a model from @a@ to @d@.
--
-- @
-- instance 'Learn' b c => Learn a d ('Dimap' b c a d l) where
--     type 'LParamMaybe' (Dimap b c a d l) = LParamMaybe l
--     type 'LStateMaybe' (Dimap b c a d l) = LStateMaybe l
-- @
type Dimap b c a d l = RMap c d (LMap b a l)

-- | Constructor for 'Dimap'
pattern DM
    :: (forall s. Reifies s W => BVar s a -> BVar s b)
    -> (forall s. Reifies s W => BVar s c -> BVar s d)
    -> l
    -> Dimap b c a d l
pattern DM { _dmPre, _dmPost, _dmLearn } = RM _dmPost (LM _dmPre _dmLearn)

instance Learn b c l => Learn a c (LMap b a l) where
    type LParamMaybe (LMap b a l) = LParamMaybe l
    type LStateMaybe (LMap b a l) = LStateMaybe l

    initParam = initParam . _lmLearn
    initState = initState . _lmLearn

    runLearn (LM f l) p x = runLearn l p (f x)
    runLearnStoch (LM f l) g p x = runLearnStoch l g p (f x)

instance Learn a b l => Learn a c (RMap b c l) where
    type LParamMaybe (RMap b c l) = LParamMaybe l
    type LStateMaybe (RMap b c l) = LStateMaybe l

    initParam = initParam . _rmLearn
    initState = initState . _rmLearn

    runLearn (RM f l) p x = first f . runLearn l p x
    runLearnStoch (RM f l) g p x = (fmap . first) f . runLearnStoch l g p x

-- | Take a model and turn it into a model that runs its output into itself
-- several times, returning the final result.  Parameterized by the number
-- of repeats, and the function to process the output to become the next
-- input.
--
-- See 'FeedbackTrace' if you want to observe all of the intermediate
-- outputs.
data Feedback :: Type -> Type -> Type -> Type where
    FB :: { _fbTimes :: Int
          , _fbFeed  :: forall s. Reifies s W => BVar s b -> BVar s a
          , _fbLearn :: l
          }
       -> Feedback a b l

-- | Construct a 'Feedback' from an endofunction (a function that returns
-- a value fo the same type as its input) by simply providing the output
-- directly as the next intput.
feedbackId :: Int -> l -> Feedback a a l
feedbackId n = FB n id

instance Learn a b l => Learn a b (Feedback a b l) where
    type LParamMaybe (Feedback a b l) = LParamMaybe l
    type LStateMaybe (Feedback a b l) = LStateMaybe l

    initParam = initParam . _fbLearn
    initState = initState . _fbLearn

    runLearn (FB n f l) p = runState
                          . foldr (>=>) go (replicate (n - 1) (fmap f . go))
      where
        go = state . runLearn l p

    runLearnStoch (FB n f l) g p = runStateT
                                 . foldr (>=>) go (replicate (n - 1) (fmap f . go))
      where
        go = StateT . runLearnStoch l g p

-- | Take a model and turn it into a model that runs its output into itself
-- several times, and returns all of the intermediate outputs.
-- Parameterized by the function to process the output to become the next
-- input.
--
-- See 'Feedback' if you only need the final result.
--
-- Compare also to 'Unroll'.
data FeedbackTrace :: Nat -> Type -> Type -> Type -> Type where
    FBT :: { _fbtFeed  :: forall s. Reifies s W => BVar s b -> BVar s a
           , _fbtLearn :: l
           }
        -> FeedbackTrace n a b l

-- | Construct a 'FeedbackTrace' from an endofunction (a function that
-- returns a value fo the same type as its input) by simply providing the
-- output directly as the next intput.
feedbackTraceId :: l -> FeedbackTrace n a a l
feedbackTraceId = FBT id

instance (Learn a b l, KnownNat n, Num b) => Learn a (SV.Vector n b) (FeedbackTrace n a b l) where
    type LParamMaybe (FeedbackTrace n a b l) = LParamMaybe l
    type LStateMaybe (FeedbackTrace n a b l) = LStateMaybe l

    initParam = initParam . _fbtLearn
    initState = initState . _fbtLearn

    runLearn (FBT f l) p x0 =
          second snd
        . runState (collectVar <$> SV.replicateM (state go))
        . (x0,)
      where
        go (x, s) = (y, (f y, s'))
          where
            (y, s') = runLearn l p x s

    runLearnStoch (FBT f l) g p x0 =
          (fmap . second) snd
        . runStateT (collectVar <$> SV.replicateM (StateT go))
        . (x0,)
      where
        go (x, s) = do
          (y, s') <- runLearnStoch l g p x s
          pure (y, (f y, s'))
