{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

module Backprop.Learn.Function (
    FixedFunc(..)
  , ParamFunc(..), compPF, parPF, idPF, fixedParam, learnParam
  , nilPF, (-~>), (-!>), (->!), (-++)
  , softMax
  , logisticFunc, scaleFunc, tanhFunc, mapFunc, reLU, eLU
  , pScale, pMap
  ) where

import           Backprop.Learn
import           Control.Category
import           Control.Monad.Primitive
import           Data.Type.Length
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Prelude hiding                        ((.), id)
import           Statistics.Distribution
import           Type.Class.Known
import           Type.Family.List
import qualified System.Random.MWC                     as MWC

newtype FixedFunc a b =
    FF { runFixedFunc :: forall s. Reifies s W => BVar s a -> BVar s b }

instance (Num a, Num b) => Learn NoParam a b (FixedFunc a b) where
    runFixed f _ = runFixedFunc f

instance Category FixedFunc where
    id = FF id
    f . g = FF $ runFixedFunc f . runFixedFunc g

data ParamFunc p a b =
    PF { _pfInit :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> m p
       , _pfFunc :: forall s. Reifies s W => BVar s p -> BVar s a -> BVar s b
       }

instance (Num p, Num a, Num b) => Learn p a b (ParamFunc p a b) where
    initParam = _pfInit
    runFixed  = _pfFunc

learnParam
    :: Learn p a b l
    => l
    -> ParamFunc p a b
learnParam l = PF { _pfInit = initParam l
                  , _pfFunc = runFixed l
                  }

fixedParam
    :: FixedFunc a b
    -> ParamFunc NoParam a b
fixedParam f = PF { _pfInit = const (pure NoParam)
                 , _pfFunc = \_ -> runFixedFunc f
                 }

idPF :: ParamFunc NoParam a a
idPF = fixedParam id

compPF
    :: (Num p, Num q)
    => ParamFunc p b c
    -> ParamFunc q a b
    -> ParamFunc (T2 p q) a c
compPF f g = PF { _pfInit = \gen -> T2 <$> _pfInit f gen <*> _pfInit g gen
                , _pfFunc = \p   -> _pfFunc f (p ^^. t2_1)
                                  . _pfFunc g (p ^^. t2_2)
                }

parPF
    :: (Num p, Num q, Num a, Num b, Num c, Num d)
    => ParamFunc p a c
    -> ParamFunc q b d
    -> ParamFunc (T2 p q) (T2 a b) (T2 c d)
parPF f g = PF { _pfInit = \gen -> T2 <$> _pfInit f gen <*> _pfInit g gen
               , _pfFunc = \p x -> isoVar2 T2 t2Tup
                    (_pfFunc f (p ^^. t2_1) (x ^^. t2_1))
                    (_pfFunc g (p ^^. t2_2) (x ^^. t2_2))
               }


nilPF :: ParamFunc (T '[]) a a
nilPF = PF { _pfInit = const (pure TNil)
           , _pfFunc = const id
           }

(-~>)
    :: (Known Length ps, ListC (Num <$> ps), Num p)
    => ParamFunc p a b
    -> ParamFunc (T ps) b c
    -> ParamFunc (T (p ': ps)) a c
f -~> fs = PF { _pfInit = \g  -> (:&) <$> _pfInit f g <*> _pfInit fs g
              , _pfFunc = \ps -> _pfFunc fs (ps ^^. tTail)
                               . _pfFunc f  (ps ^^. tHead)
              }
infixr 5 -~>

(-!>)
    :: FixedFunc a b
    -> ParamFunc p b c
    -> ParamFunc p a c
f -!> g = PF { _pfInit = _pfInit g
             , _pfFunc = \p -> _pfFunc g p . runFixedFunc f
             }
infixr 5 -!>

(->!)
    :: ParamFunc p a b
    -> FixedFunc b c
    -> ParamFunc p a c
f ->! g = PF { _pfInit = _pfInit f
             , _pfFunc = \p -> runFixedFunc g . _pfFunc f p
             }
infixr 5 ->!

(-++)
    :: forall ps qs a b c. (Known Length ps, Known Length qs, ListC (Num <$> ps), ListC (Num <$> qs))
    => ParamFunc (T ps) a b
    -> ParamFunc (T qs) b c
    -> ParamFunc (T (ps ++ qs)) a c
fs -++ gs = PF { _pfInit = \g  -> tAppend <$> _pfInit fs g <*> _pfInit gs g
               , _pfFunc = \ps -> _pfFunc gs (ps ^^. tDrop @ps @qs known)
                                . _pfFunc fs (ps ^^. tTake @ps @qs known)
               }
infixr 5 -++

softMax :: KnownNat i => FixedFunc (R i) (R i)
softMax = FF $ \x ->  let expx = exp x
                      in  expx / konst (norm_1V expx)


logisticFunc :: Floating a => FixedFunc a a
logisticFunc = FF $ \x -> 1 / (1 + exp (-x))

scaleFunc :: Num a => a -> FixedFunc a a
scaleFunc c = FF (* constVar c)

tanhFunc :: Floating a => FixedFunc a a
tanhFunc = FF tanh

mapFunc
    :: KnownNat i
    => (forall s. Reifies s W => BVar s Double -> BVar s Double)
    -> FixedFunc (R i) (R i)
mapFunc f = FF (vmap' f)

reLU :: KnownNat i => FixedFunc (R i) (R i)
reLU = mapFunc $ \x -> if x < 0 then 0 else x

eLU :: KnownNat i => FixedFunc (R i) (R i)
eLU = mapFunc $ \x -> if x < 0 then exp x - 1 else x

pScale :: (KnownNat i, ContGen d) => d -> ParamFunc Double (R i) (R i)
pScale d = PF { _pfInit = genContVar d
              , _pfFunc = \p x -> konst p * x
              }

pMap
    :: KnownNat i
    => (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m p)
    -> (forall s. Reifies s W => BVar s p -> BVar s Double -> BVar s Double)
    -> ParamFunc p (R i) (R i)
pMap i f = PF { _pfInit = i
              , _pfFunc = \p -> vmap (f p)
              }
