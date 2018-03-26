{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}

module Backprop.Learn.Function (
    FixedFunc(..)
  , ParamFunc(..), compPF, parPF, idPF
  , softMax
  , logisticMap, scaleMap, tanhMap
  , PFChain(..), (-++)
  ) where

import           Backprop.Learn
import           Control.Category
import           Control.Monad.Primitive
import           Data.Kind
import           Data.Type.Length
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop hiding ((<>))
import           Prelude hiding                               ((.), id)
import           Type.Class.Known
import           Type.Family.List
import qualified System.Random.MWC                            as MWC

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

compPF
    :: (Num p, Num q)
    => ParamFunc p b c
    -> ParamFunc q a b
    -> ParamFunc (T2 p q) a c
compPF f g = PF { _pfInit = \gen -> T2 <$> _pfInit f gen <*> _pfInit g gen
                , _pfFunc = \p   -> _pfFunc f (p ^^. t2_1)
                                  . _pfFunc g (p ^^. t2_2)
                }

idPF :: ParamFunc NoParam a a
idPF = PF { _pfInit = const (pure NoParam)
          , _pfFunc = \_ -> id
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

data PFChain :: [Type] -> Type -> Type -> Type where
    PFCNil :: PFChain '[] a a
    (:-?>) :: Num b
           => ParamFunc p a b
           -> PFChain ps b c
           -> PFChain (p ': ps) a c
    (:-!>) :: Num b
           => FixedFunc a b
           -> PFChain ps b c
           -> PFChain ps a c
infixr 5 :-?>
infixr 5 :-!>

instance (Known Length ps, ListC (Num <$> ps), Num a, Num b)
      => Learn (T ps) a b (PFChain ps a b) where
    initParam = \case
      PFCNil      -> \_ -> pure TNil
      pf :-?> pcs -> \g -> (:&) <$> initParam pf g
                                <*> initParam pcs g
      _  :-!> pcs -> initParam pcs

    runFixed = \case
      PFCNil      -> const id
      pf :-?> pcs -> \ps -> runFixed pcs (ps ^^. tTail)
                          . runFixed pf  (ps ^^. tHead)
      ff :-!> pcs -> \ps -> runFixed pcs ps
                          . runFixedFunc ff

(-++) :: PFChain ps a b -> PFChain qs b c -> PFChain (ps ++ qs) a c
(-++) = \case
    PFCNil      -> id
    pf :-?> pcs -> (pf :-?>) . (pcs -++)
    ff :-!> pcs -> (ff :-!>) . (pcs -++)
infixr 4 -++

softMax :: KnownNat i => FixedFunc (R i) (R i)
softMax = FF $ \x ->  let expx = exp x
                      in  expx / konst (norm_1V expx)


logisticMap :: Floating a => FixedFunc a a
logisticMap = FF $ \x -> 1 / (1 + exp (-x))

scaleMap :: Num a => a -> FixedFunc a a
scaleMap c = FF (* constVar c)

tanhMap :: Floating a => FixedFunc a a
tanhMap = FF tanh

-- reLU :: FixedMap i
-- reLU = FM $ \x -> if x < 0 then

    -- MF_Ident :: CommonMap
    -- MF_Scale :: a -> CommonMap
    -- MF_Logit :: CommonMap
    -- MF_Tanh  :: CommonMap
    -- MF_ReLU  :: CommonMap
    -- MF_ReLUp :: a -> CommonMap
    -- MF_ELU   :: CommonMap
    -- MF_ELUp  :: a -> CommonMap
