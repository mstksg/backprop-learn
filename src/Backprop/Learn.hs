{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ViewPatterns           #-}

module Backprop.Learn (
    module L
  , Chain(..), (~:++)
  , LearnFunc(..), learnFunc, (~>), nilLF, (~!++), (~++!), (~++)
) where

import           Backprop.Learn.Class    as L
import           Control.Monad
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Type.Length
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Type.Class.Known
import           Type.Family.List
import qualified System.Random.MWC       as MWC

-- | Chain components linearly, retaining the ability to deconstruct at
-- a later time.
data Chain :: [Type] -> [Type] -> Type -> Type -> Type where
    CNil  :: Chain '[] '[] a a
    (:~>) :: (Learn p a b l, Num b)
          => l
          -> Chain ls ps b c
          -> Chain (l ': ls) (p ': ps) a c
infixr 5 :~>

instance (ListC (Num <$> ps), Known Length ps, Num a, Num b)
      => Learn (T ps) a b (Chain ls ps a b) where
    initParam = \case
      CNil     -> \_ -> pure TNil
      l :~> ls -> \g -> (:&) <$> initParam l  g
                             <*> initParam ls g

    runFixed = \case
      CNil     -> \_ -> id
      l :~> ls -> \ps -> runFixed ls (ps ^^. tTail)
                       . runFixed l  (ps ^^. tHead)

    runStoch = \case
      CNil     -> \_ _ -> pure
      l :~> ls -> \g ps -> runStoch ls g (ps ^^. tTail)
                       <=< runStoch l  g (ps ^^. tHead)

(~:++)
    :: forall ls ks ps qs a b c. (Known Length ps, Known Length qs, ListC (Num <$> ps), ListC (Num <$> qs))
    => Chain ls ps a b
    -> Chain ks qs b c
    -> Chain (ls ++ ks) (ps ++ qs) a c
CNil       ~:++ ys = ys
(x :~> xs) ~:++ ys = x :~> (xs ~:++ ys)
infixl 5 ~:++

-- | Data type representing trainable models.
--
-- Useful for performant composition, but you lose the ability to decompose
-- parts.
data LearnFunc :: Type -> Type -> Type -> Type where
    LF :: { _lfInitParam :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m p
          , _lfRunFixed  :: forall s. Reifies s W => BVar s p -> BVar s a -> BVar s b
          , _lfRunStoch
                :: forall m s. (PrimMonad m, Reifies s W)
                => MWC.Gen (PrimState m)
                -> BVar s p
                -> BVar s a
                -> m (BVar s b)
          }
       -> LearnFunc p a b

instance (Num p, Num a, Num b) => Learn p a b (LearnFunc p a b) where
    initParam = _lfInitParam
    runFixed  = _lfRunFixed
    runStoch  = _lfRunStoch

learnFunc :: Learn p a b l => l -> LearnFunc p a b
learnFunc l = LF { _lfInitParam = initParam l
                 , _lfRunFixed  = runFixed l
                 , _lfRunStoch  = runStoch l
                 }

nilLF :: LearnFunc (T '[]) a a
nilLF = LF { _lfInitParam = const (pure TNil)
           , _lfRunFixed  = const id
           , _lfRunStoch  = \_ -> const pure
           }

(~>)
    :: (Num p, ListC (Num <$> ps), Known Length ps)
    => LearnFunc p a b
    -> LearnFunc (T ps) b c
    -> LearnFunc (T (p ': ps)) a c
l ~> ls = LF { _lfInitParam = \g  -> (:&) <$> _lfInitParam l  g
                                          <*> _lfInitParam ls g
             , _lfRunFixed  = \ps -> _lfRunFixed ls (ps ^^. tTail)
                                   . _lfRunFixed l  (ps ^^. tHead)
             , _lfRunStoch  = \g ps -> _lfRunStoch ls g (ps ^^. tTail)
                                   <=< _lfRunStoch l  g (ps ^^. tHead)
             }
infixr 5 ~>

(~!++)
    :: LearnFunc NoParam a b
    -> LearnFunc (T ps) b c
    -> LearnFunc (T ps) a c
ls ~!++ ks = LF { _lfInitParam = _lfInitParam ks
                , _lfRunFixed  = \ps -> _lfRunFixed ks ps
                                      . _lfRunFixed ls (constVar NoParam)
                , _lfRunStoch  = \g ps -> _lfRunStoch ks g ps
                                      <=< _lfRunStoch ls g (constVar NoParam)
                }
infixr 5 ~!++

(~++!)
    :: LearnFunc (T ps) a b
    -> LearnFunc NoParam b c
    -> LearnFunc (T ps) a c
ls ~++! ks = LF { _lfInitParam = _lfInitParam ls
                , _lfRunFixed  = \ps -> _lfRunFixed ks (constVar NoParam)
                                      . _lfRunFixed ls ps
                , _lfRunStoch  = \g ps -> _lfRunStoch ks g (constVar NoParam)
                                      <=< _lfRunStoch ls g ps
                }
infixr 5 ~++!

(~++)
    :: forall ps qs a b c. (Known Length ps, Known Length qs, ListC (Num <$> ps), ListC (Num <$> qs))
    => LearnFunc (T ps) a b
    -> LearnFunc (T qs) b c
    -> LearnFunc (T (ps ++ qs)) a c
ls ~++ ks = LF { _lfInitParam = \g -> tAppend <$> _lfInitParam ls g
                                              <*> _lfInitParam ks g
               , _lfRunFixed  = \ps -> _lfRunFixed ks (ps ^^. tDrop @ps @qs known)
                                     . _lfRunFixed ls (ps ^^. tTake @ps @qs known)
               , _lfRunStoch  = \g ps -> _lfRunStoch ks g (ps ^^. tDrop @ps @qs known)
                                     <=< _lfRunStoch ls g (ps ^^. tTake @ps @qs known)
               }

