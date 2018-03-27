{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Backprop.Learn.Function (
    ParamFunc(.., FF), FixedFunc
  , learnParam
  , softMax
  , logisticFunc
  , scaleFunc
  , tanhFunc
  , mapFunc
  , reLU
  , eLU
  , pScale
  , pMap
  , (.-), nilPF, onlyPF
  ) where

import           Backprop.Learn.Class
import           Control.Applicative
import           Control.Category
import           Control.Monad.Primitive
import           Data.Type.Length
import           Data.Type.Mayb
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Prelude hiding                        ((.), id)
import           Statistics.Distribution
import           Type.Class.Higher
import           Type.Class.Known
import           Type.Class.Witness
import           Type.Family.List
import qualified System.Random.MWC                     as MWC

-- | An unparameterized function.  Has a 'Category' instance.
type FixedFunc = ParamFunc 'Nothing

pattern FF :: (forall s. Reifies s W => BVar s a -> BVar s b) -> FixedFunc a b
pattern FF f <- (getFF->f) where
    FF f = PF { _pfInit = const N_
              , _pfFunc = const f
              }

getFF :: forall a b. FixedFunc a b -> (forall s. Reifies s W => BVar s a -> BVar s b)
getFF ff = _pfFunc ff N_

-- | A @'ParamFunc' p a b@ is a parameterized function from @a@ to @b@,
-- potentially with trainable parameter @p@.
data ParamFunc p a b =
    PF { _pfInit :: forall m. PrimMonad m => MWC.Gen (PrimState m) -> Mayb m p
       , _pfFunc :: forall s. Reifies s W => Mayb (BVar s) p -> BVar s a -> BVar s b
       }

instance (Num a, Num b, MaybeC Num p, KnownMayb p) => Learn a b (ParamFunc p a b) where
    type LParamMaybe (ParamFunc p a b) = p

    initParam = _pfInit
    runLearn p = stateless . _pfFunc p

instance (MaybeC Num p, KnownMayb p) => Category (ParamFunc p) where
    id = PF { _pfInit = \_ -> map1 (pure 0 \\) $ maybeWit @_ @Num
            , _pfFunc = \_ -> id
            }
    f . g = PF { _pfInit = \gen -> zipMayb3 (liftA2 (+) \\)
                                     (maybeWit @_ @Num)
                                     (_pfInit f gen)
                                     (_pfInit g gen)
               , _pfFunc = \p -> _pfFunc f p
                               . _pfFunc g p
               }

-- | Create a 'ParamFunc' from any instance of 'Learn' that does not have
-- state.
learnParam
    :: forall l a b. (Learn a b l, NoState l)
    => l
    -> ParamFunc (LParamMaybe l) a b
learnParam l = PF { _pfInit = initParam l
                  , _pfFunc = runLearnStateless l
                  }

-- | 'ParamFunc' taking a singleton list; meant to be used with '.-'
onlyPF
    :: forall p a b. (KnownMayb p, MaybeC Num p)
    => ParamFunc p a b
    -> ParamFunc ('Just (T (MaybeToList p))) a b
onlyPF f = PF { _pfInit = J_
                        . fmap prodT
                        . traverse1 (fmap I)
                        . maybToList
                        . _pfInit f
              , _pfFunc = \(J_ ps) -> case knownMayb @p of
                                   N_   -> _pfFunc f N_
                                   J_ _ -> _pfFunc f (J_ (isoVar tOnly onlyT ps))
              }
  

-- | Compose two 'ParamFunc's on lists.
(.-)
    :: forall ps qs a b c. (ListC (Num <$> ps), ListC (Num <$> qs), Known Length ps, Known Length qs)
    => ParamFunc ('Just (T ps)) b c
    -> ParamFunc ('Just (T qs)) a b
    -> ParamFunc ('Just (T (ps ++ qs))) a c
f .- g = PF { _pfInit = \gen -> J_ $ tAppend <$> fromJ_ (_pfInit f gen)
                                             <*> fromJ_ (_pfInit g gen)
            , _pfFunc = \(J_ ps) -> _pfFunc f (J_ (ps ^^. tTake @ps @qs known))
                                  . _pfFunc g (J_ (ps ^^. tDrop @ps @qs known))
            }
infixr 9 .-

-- | The identity of '.-'
nilPF :: ParamFunc ('Just (T '[])) a a
nilPF = id

-- | Softmax normalizer
softMax :: KnownNat i => FixedFunc (R i) (R i)
softMax = FF $ \x -> let expx = exp x
                     in  expx / konst (norm_1V expx)

-- | Logistic function, typically used as an activation function
logisticFunc :: Floating a => FixedFunc a a
logisticFunc = FF $ \x -> 1 / (1 + exp (-x))

-- | Scaling function
scaleFunc :: Num a => a -> FixedFunc a a
scaleFunc c = FF (* constVar c)

-- | Tanh function
tanhFunc :: Floating a => FixedFunc a a
tanhFunc = FF tanh

-- | Map a differentiable function over every item in an 'R'
mapFunc
    :: KnownNat i
    => (forall s. Reifies s W => BVar s Double -> BVar s Double)
    -> FixedFunc (R i) (R i)
mapFunc f = FF (vmap' f)

-- | Rectified linear unit activation function
reLU :: KnownNat i => FixedFunc (R i) (R i)
reLU = mapFunc $ \x -> if x < 0 then 0 else x

-- | Exponential linear unit activation function
eLU :: KnownNat i => FixedFunc (R i) (R i)
eLU = mapFunc $ \x -> if x < 0 then exp x - 1 else x

-- | Scaling function, but with a trainable scaling parameter.
pScale :: (KnownNat i, ContGen d) => d -> ParamFunc ('Just Double) (R i) (R i)
pScale d = PF { _pfInit = J_ . genContVar d
              , _pfFunc = (*) . konst . fromJ_
              }

-- | Map a parameterized differentiable function over ever item in an 'R'.
-- The parameteri is trainable.
pMap
    :: (KnownNat i, Num p)
    => (forall m. PrimMonad m => MWC.Gen (PrimState m) -> m p)
    -> (forall s. Reifies s W => BVar s p -> BVar s Double -> BVar s Double)
    -> ParamFunc ('Just p) (R i) (R i)
pMap i f = PF { _pfInit = J_ . i
              , _pfFunc = vmap . f . fromJ_
              }

-- TODO: vmap can do better.
