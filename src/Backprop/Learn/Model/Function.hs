{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
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

module Backprop.Learn.Model.Function (
  -- * Types
    ParamFunc(..)
  , ParamFuncP, pattern PFP, runParamFuncP
  , FixedFunc, pattern FF, runFixedFunc
  , paramMap, learnParam
  , idLearn
  -- ** Combinators
  , dimapPF, lmapPF, rmapPF, compPF, parPF
  -- *** Chain
  , (.-), nilPF, onlyPF
  -- * Activation functions
  -- | See <https://en.wikipedia.org/wiki/Activation_function>
  --
  -- ** Maps
  -- *** Unparameterized
  , step
  , logistic
  , softsign
  , reLU
  , softPlus
  , bentIdentity
  , siLU
  , softExponential
  , sinc
  , gaussian
  , tanh
  , atan
  , sin
  , vmap
  , vmap'
  -- *** Parameterized
  , liftUniform
  , isru
  , preLU
  , sreLU
  , sreLUPFP
  , eLU
  , isrLU
  , apl
  , aplPFP
  -- ** Mixing
  , softMax
  , maxout
  , kSparse
  ) where

import           Backprop.Learn.Model.Class
import           Control.Category
import           Data.Foldable
import           Data.Proxy
import           Data.Type.Length
import           Data.Type.Mayb hiding                        (type (<$>))
import           Data.Typeable
import           GHC.TypeNats
import           Numeric.Backprop
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop hiding (tr)
import           Prelude hiding                               ((.), id)
import           Type.Class.Known
import           Type.Family.List
import qualified Data.Vector.Sized                            as SV
import qualified Data.Vector.Storable.Sized                   as SVS
import qualified Numeric.LinearAlgebra                        as HU
import qualified Numeric.LinearAlgebra.Static                 as H
import qualified Numeric.LinearAlgebra.Static.Vector          as H

-- | An unparameterized function.  Has a 'Category' instance.
--
-- A @'FixedFunc' a b@ essentially the same as a:
--
-- @
-- forall s. 'Reifies' s 'W' => 'BVar' s a -> 'BVar' s b
-- @
--
-- And the 'FF' pattern (and 'runFixedFunc' extractor) witness this.
--
-- It is usually better to just use the functions directly, with
-- combinators like 'Dimap', 'LMap', 'RMap', 'dimapPF', 'lmapPF', 'rmapPF',
-- etc.  This is just provided to let you work nicely with 'ParamFunc'
-- combinators.
type FixedFunc = ParamFunc 'Nothing

-- | 'FF' and 'runFixedFunc' witness the fact that a @'FixedFunc' a b@ is
-- just a function from @'BVar' s a@ to @'BVar' s b@.
pattern FF :: (forall s. Reifies s W => BVar s a -> BVar s b) -> FixedFunc a b
pattern FF { runFixedFunc } <- (getFF->runFixedFunc) where
    FF f = PF (const f)
{-# COMPLETE FF #-}

getFF :: forall a b. FixedFunc a b -> (forall s. Reifies s W => BVar s a -> BVar s b)
getFF ff = runParamFunc ff N_

-- | Identity model, useful for using with other combinators.
idLearn :: FixedFunc a a
idLearn = FF id

-- | A @'ParamFunc' p a b@ is a parameterized function from @a@ to @b@,
-- potentially with trainable parameter @p@.
--
-- A utility wrapper for a deterministic and stateless model.
newtype ParamFunc p a b =
    PF { runParamFunc :: forall s. Reifies s W => Mayb (BVar s) p -> BVar s a -> BVar s b
       }
  deriving (Typeable)

instance ( Num a, Num b, MaybeC Num p, KnownMayb p)
      => Learn a b (ParamFunc p a b) where
    type LParamMaybe (ParamFunc p a b) = p

    runLearn p = stateless . runParamFunc p

instance Category (ParamFunc p) where
    id = PF (const id)
    f . g = PF $ \p -> runParamFunc f p
                     . runParamFunc g p

-- | Convenient type synonym for a 'ParamFunc' with parameters.
--
-- Mostly made to be easy to construct/deconstruct with 'PFP' and
-- 'runParamFuncP'.
type ParamFuncP p = ParamFunc ('Just p)

pattern PFP :: (forall s. Reifies s W => BVar s p -> BVar s a -> BVar s b)
            -> ParamFuncP p a b
pattern PFP { runParamFuncP } <- (getPFP->(getWF->runParamFuncP))
  where
    PFP f = PF $ \(J_ p) -> f p
{-# COMPLETE PFP #-}

newtype WrapFun p a b = WF { getWF :: forall s. Reifies s W => BVar s p -> BVar s a -> BVar s b }

getPFP :: ParamFuncP p a b -> WrapFun p a b
getPFP pf = WF (\case p -> runParamFunc pf (J_ p))

-- | Create a 'ParamFunc' from any instance of 'Learn' that does not have
-- state.
learnParam
    :: forall l a b. (Learn a b l, NoState l)
    => l
    -> ParamFunc (LParamMaybe l) a b
learnParam l = PF (runLearnStateless l)

-- | 'ParamFuncP' taking a singleton list; meant to be used with '.-'
onlyPF
    :: forall p a b. (KnownMayb p, MaybeC Num p)
    => ParamFunc p a b
    -> ParamFuncP (T (MaybeToList p)) a b
onlyPF f = PFP $ \ps -> case knownMayb @p of
                          N_   -> runParamFunc f N_
                          J_ _ -> runParamFunc f (J_ (isoVar tOnly onlyT ps))


-- | Compose two 'ParamFuncP's on lists.
(.-)
    :: forall ps qs a b c. (ListC (Num <$> ps), ListC (Num <$> qs), Known Length ps, Known Length qs)
    => ParamFuncP (T ps) b c
    -> ParamFuncP (T qs) a b
    -> ParamFuncP (T (ps ++ qs)) a c
f .- g = PFP $ \ps -> runParamFuncP f (ps ^^. tTake @ps @qs known)
                    . runParamFuncP g (ps ^^. tDrop @ps @qs known)
infixr 9 .-

-- | The identity of '.-'
nilPF :: ParamFuncP (T '[]) a a
nilPF = id

-- | Pre- and post-compose a 'ParamFunc'
dimapPF
    :: (forall s. Reifies s W => BVar s a -> BVar s b)
    -> (forall s. Reifies s W => BVar s c -> BVar s d)
    -> ParamFunc p b c
    -> ParamFunc p a d
dimapPF f g h = PF $ \p -> g . runParamFunc h p . f

-- | Precompose a 'ParamFunc'
lmapPF
    :: (forall s. Reifies s W => BVar s a -> BVar s b)
    -> ParamFunc p b c
    -> ParamFunc p a c
lmapPF f = dimapPF f id

-- | Postcompose a 'ParamFunc'
rmapPF
    :: (forall s. Reifies s W => BVar s b -> BVar s c)
    -> ParamFunc p a b
    -> ParamFunc p a c
rmapPF = dimapPF id

-- | Compose two 'ParamFunc's sequentially
compPF
    :: forall p q a b c. (MaybeC Num p, MaybeC Num q, KnownMayb p, KnownMayb q)
    => ParamFunc p a b
    -> ParamFunc q b c
    -> ParamFunc (TupMaybe p q) a c
compPF f g = PF $ \pq ->
    let (p, q) = splitTupMaybe @_ @p @q
            (\pq' -> (pq' ^^. t2_1, pq' ^^. t2_2)) pq
    in  runParamFunc g q . runParamFunc f p

-- | Compose two 'ParamFunc's in parallel
parPF
    :: forall p q a b c d. (MaybeC Num p, MaybeC Num q, KnownMayb p, KnownMayb q, Num a, Num b, Num c, Num d)
    => ParamFunc p a c
    -> ParamFunc q b d
    -> ParamFunc (TupMaybe p q) (T2 a b) (T2 c d)
parPF f g = PF $ \pq xy ->
    let (p, q) = splitTupMaybe @_ @p @q
            (\pq' -> (pq' ^^. t2_1, pq' ^^. t2_2)) pq
    in  isoVar2 T2 t2Tup (runParamFunc f p (xy ^^. t2_1))
                         (runParamFunc g q (xy ^^. t2_2))

-- TODO: replace all of these with manual ops?

-- | Softmax normalizer
softMax
    :: (KnownNat i, Reifies s W)
    => BVar s (R i)
    -> BVar s (R i)
softMax x = expx / konst (norm_1V expx)
  where
    expx = exp x

-- | Logistic function
--
-- \[
-- \sigma(x) = \frac{1}{1 + e^{-x}}
-- \]
logistic :: Floating a => a -> a
logistic x = 1 / (1 + exp (-x))

-- | Binary step / heaviside step
--
-- To use with vectors ('R'), use 'vmap''.
--
-- \[
-- \begin{cases}
-- 0 & \text{for } x < 0 \\
-- 1 & \text{for } x \ge 0
-- \end{cases}
-- \]
step :: (Ord a, Num a) => a -> a
step x | x < 0     = 0
       | otherwise = 1

-- | Softsign activation function
--
-- \[
-- \frac{x}{1 + \lvert x \rvert}
-- \]
softsign :: Fractional a => a -> a
softsign x = x / (1 + abs x)

-- | Inverse square root unit
--
-- \[
-- \frac{x}{\sqrt{1 + \alpha x^2}}
-- \]
--
-- See 'liftUniform' to make this compatible with 'PFP'.
--
-- You can also just use this after partially applying it, to fix the
-- parameter (and not have it trained).
isru
    :: Floating a
    => a        -- ^ α (scaling parameter)
    -> a        -- ^ x
    -> a
isru α x = x / sqrt (1 + α * x * x)

-- | Rectified linear unit.
--
-- To use with vectors ('R'), use 'vmap''.
--
--
-- \[
-- \max(0,x)
-- \]
--
-- @
-- 'reLU' = 'preLU' 0
-- @
--
reLU :: (Num a, Ord a) => a -> a
reLU x | x < 0     = 0
       | otherwise = x

-- | Parametric rectified linear unit
--
-- To use with vectors ('R'), use 'vmap''.
--
-- If scaling parameter is a fixed (and not learned) parameter, this is
-- typically called a leaky recitified linear unit (typically with
-- α = 0.01).
--
-- To use as a learned parameter:
--
-- @
-- 'vmap' . 'preLU' :: 'BVar' s Double -> 'BVar' s ('R' n) -> BVar s (R n)
-- @
--
-- This can be give directly to 'PFP'.
--
-- To fix the paramater ("leaky"), just partially apply a parameter:
--
-- @
-- 'preLU' 0.01           :: 'BVar' s ('R' n) -> BVar s (R n)
-- preLU ('realToFrac' α) :: BVar s (R n) -> BVar s (R n)
-- @
--
-- See also 'rreLU'.
--
-- \[
-- \begin{cases}
-- \alpha x & \text{for } x < 0 \\
-- x        & \text{for } x \ge 0
-- \end{cases}
-- \]
preLU
    :: (Num a, Ord a)
    => a        -- ^ α (scaling parameter)
    -> a        -- ^ x
    -> a
preLU α x | x < 0     = α * x
          | otherwise = x

-- | Exponential linear unit
--
-- To use as a learned parameter:
--
-- @
-- 'vmap' . 'eLU' :: 'BVar' s Double -> 'BVar' s ('R' n) -> BVar s (R n)
-- @
--
-- This can be give directly to 'PFP'.
--
-- To fix the paramater, just partially apply a parameter:
--
-- @
-- 'eLU' 0.01 :: 'BVar' s ('R' n) -> BVar s (R n)
-- @
--
-- \[
-- \begin{cases}
-- \alpha (e^x - 1) & \text{for } x < 0 \\
-- x                & \text{for } x \ge 0
-- \end{cases}
-- \]
eLU :: (Floating a, Ord a)
    => a        -- ^ α (scaling parameter)
    -> a        -- ^ x
    -> a
eLU α x | x < 0     = α * (exp x - 1)
        | otherwise = x

-- | S-shaped rectified linear activiation unit
--
-- See 'sreLUPFP' for an uncurried and uniformly lifted version usable with
-- 'PFP'.
--
-- \[
-- \begin{cases}
-- t_l + a_l (x - t_l) & \text{for } x \le t_l  \\
-- x                   & \text{for } t_l < x < t_r  \\
-- t_r + a_r (x - t_r) & \text{for } x \ge t_r
-- \end{cases}
-- \]
sreLU
    :: (Num a, Ord a)
    => a        -- ^ @t_l@
    -> a        -- ^ @a_l@
    -> a        -- ^ @t_r@
    -> a        -- ^ @a_l@
    -> a        -- ^ @x@
    -> a
sreLU tl al tr ar x
    | x < tl    = tl + al * (x - tl)
    | x > tr    = tr + ar * (x - tr)
    | otherwise = x

-- | An uncurried and uniformly lifted version of 'sreLU' directly usable
-- with 'PFP'.
sreLUPFP
    :: (KnownNat n, Reifies s W)
    => BVar s (T2 (T2 Double Double) (T2 Double Double))
    -> BVar s (R n)
    -> BVar s (R n)
sreLUPFP taltar = vmap $ sreLU (tal ^^. t2_1) (tal ^^. t2_2)
                               (tar ^^. t2_1) (tar ^^. t2_2)
  where
    tal = taltar ^^. t2_1
    tar = taltar ^^. t2_2

-- | Inverse square root linear unit
--
-- To use with vectors ('R'), use 'vmap''.
--
-- \[
-- \begin{cases}
-- \frac{x}{1 + \alpha x^2} & \text{for } x < 0 \\
-- x                        & \text{for } x \ge 0
-- \end{cases}
-- \]
isrLU
    :: (Floating a, Ord a)
    => a        -- ^ α
    -> a        -- ^ x
    -> a
isrLU α x
    | x < 0     = x / sqrt (1 + α * x * x)
    | otherwise = x

-- | Adaptive piecewise linear activation unit
--
-- See 'aplPFP' for an uncurried version usable with 'PFP'.
--
-- \[
-- \max(0, x_i) + \sum_j^M a_i^j \max(0, -x_i + b_i^j)
-- \]
apl :: (KnownNat n, KnownNat m, Reifies s W)
    => BVar s (L n m)     -- ^ a
    -> BVar s (L n m)     -- ^ b
    -> BVar s (R m)       -- ^ x
    -> BVar s (R m)
apl as bs x = vmap' (max 0) x
            + sum (toRows (as * (bs - fromRows (SV.replicate x))))

-- | 'apl' uncurried, to be directly usable with 'PFP'.
aplPFP
    :: (KnownNat n, KnownNat m, Reifies s W)
    => BVar s (T2 (L n m) (L n m))
    -> BVar s (R m)
    -> BVar s (R m)
aplPFP ab = apl (ab ^^. t2_1) (ab ^^. t2_2)

-- | SoftPlus
--
-- \[
-- \ln(1 + e^x)
-- \]
softPlus :: Floating a => a -> a
softPlus x = log (1 + exp x)

-- | Bent identity
--
-- \[
-- \frac{\sqrt{x^2 + 1} - 1}{2} + x
-- \]
bentIdentity :: Floating a => a -> a
bentIdentity x = (sqrt (x * x + 1) - 1) / 2 + x

-- | Sigmoid-weighted linear unit.  Multiply 'logistic' by its input.
--
-- \[
-- x \sigma(x)
-- \]
siLU :: Floating a => a -> a
siLU x = x * logistic x

-- | SoftExponential
--
-- To use with vectors ('R'), use 'vmap''.
--
-- \[
-- \begin{cases}
-- - \frac{\ln(1 - \alpha (x + \alpha))}{\alpha} & \text{for } \alpha < 0  \\
-- x                                             & \text{for } \alpha = 0  \\
-- \frac{e^{\alpha x} - 1}{\alpha} + \alpha      & \text{for } \alpha > 0
-- \end{cases}
-- \]
softExponential
    :: (Floating a, Ord a)
    => a            -- ^ α
    -> a            -- ^ x
    -> a
softExponential α x = case compare α x of
    LT -> - log (1 - α * (x + α)) / α
    EQ -> x
    GT -> (exp (α * x) - 1) / α + α

-- | Sinc
--
-- \[
-- \begin{cases}
-- 1                 & \text{for } x = 0  \\
-- \frac{\sin(x)}{x} & \text{for } x \ne 0
-- \end{cases}
-- \]
sinc :: (Floating a, Eq a) => a -> a
sinc 0 = 1
sinc x = sin x / x

-- | Gaussian
--
-- \[
-- e^{-x^2}
-- \]
gaussian :: Floating a => a -> a
gaussian x = exp (- (x * x))

-- | Maximum of vector.
--
-- Compare to 'norm_InfV', which gives the maximum absolute value.
maxout :: (KnownNat n, Reifies s W) => BVar s (R n) -> BVar s Double
maxout = liftOp1 . op1 $ \x ->
    let n = HU.maxElement . H.extract $ x
    in  ( n
        , \d -> H.vecR . SVS.map (\e -> if e == n then d else 0) . H.rVec $ x
        )

-- | Usable with functions like '*', 'isru', etc. to turn them into a form
-- usable with 'PFP':
--
-- @
-- 'liftUniform' ('*')  :: 'BVar' s 'Double' -> BVar s ('R' n) -> BVar s (R n)
-- liftUniform 'isru' :: BVar s Double -> BVar s (R n) -> BVar s (R n)
-- @
--
-- Basically turns a parmaeterized function on individual elements of
-- into one that shares the same parameter across all elements of the
-- vector.
liftUniform
    :: (Reifies s W, KnownNat n)
    => (BVar s (R n) -> r)
    -> BVar s Double
    -> r
liftUniform f = f . konst

-- | Utility function to make a 'ParamFunc' that maps a parameterized
-- function over every item in the 'R'.  The parameter is shared across the
-- entire map, and trained.
paramMap
    :: KnownNat i
    => (forall s. Reifies s W => Mayb (BVar s) p -> BVar s Double -> BVar s Double)
    -> ParamFunc p (R i) (R i)
paramMap f = PF (vmap . f)

-- -- TODO: vmap can do better.

-- | Keep only the top @k@ values, and zero out all of the rest.
--
-- Useful for postcomposing in between layers (with a logistic function
-- before) to encourage the number of "activated" neurons is kept to be
-- around @k@.  Used in k-Sprase autoencoders (see 'KAutoencoder').
--
-- <http://www.ericlwilkinson.com/blog/2014/11/19/deep-learning-sparse-autoencoders>
kSparse
    :: forall n s. (Reifies s W, KnownNat n)
    => Int                      -- ^ number of items to keep
    -> BVar s (R n)
    -> BVar s (R n)
kSparse k = liftOp1 . op1 $ \xs ->
    let xsSort = HU.sortVector (H.extract xs)
        thresh = xsSort `HU.atIndex` (n - k)
        mask   = H.dvmap (\x -> if x >= thresh then 1 else 0) xs
    in  ( H.dvmap (\x -> if x >= thresh then x else 0) xs
        , (* mask)
        )
  where
    n = fromIntegral $ natVal (Proxy @n)
