{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
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
  -- * Statistics
    meanModel
  , varModel
  , stdevModel
  , rangeModel
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

import           Control.Category
import           Data.Foldable
import           Data.Profunctor
import           Data.Proxy
import           Data.Type.Tuple
import           GHC.TypeNats
import           Numeric.Backprop hiding                      (Rec(..))
import           Numeric.LinearAlgebra.Static.Backprop hiding (tr)
import           Prelude hiding                               ((.), id)
import qualified Control.Foldl                                as F
import qualified Data.Vector.Sized                            as SV
import qualified Data.Vector.Storable.Sized                   as SVS
import qualified Numeric.LinearAlgebra                        as HU
import qualified Numeric.LinearAlgebra.Static                 as H
import qualified Numeric.LinearAlgebra.Static.Vector          as H

meanModel
    :: (Backprop (t a), Foldable t, Functor t, Fractional a, Reifies s W)
    => BVar s (t a)
    -> BVar s a
meanModel = liftOp1 . op1 $ \xs ->
    let x :& n = F.fold ((:&) <$> F.sum <*> F.length) xs
    in  (x / fromIntegral n, \d -> (d / fromIntegral n) <$ xs)

varModel
    :: (Backprop (t a), Foldable t, Functor t, Fractional a, Reifies s W)
    => BVar s (t a)
    -> BVar s a
varModel = liftOp1 . op1 $ \xs ->
    let x2 :& x1 :& x0 = F.fold ((\x2' x1' x0' -> x2' :& x1' :& x0') <$> lmap (^(2::Int)) F.sum <*> F.sum <*> F.length) xs
        meanx  = x1 / fromIntegral x0
        subAll = 2 * x1 / (fromIntegral x0 ^ (2 :: Int))
    in  ( (x2 / fromIntegral x0) - meanx * meanx
        , \d -> let subAllD = d * subAll
                in  (\x -> d * 2 * x / fromIntegral x0 - subAllD) <$> xs
        )

stdevModel
    :: (Backprop (t a), Foldable t, Functor t, Floating a, Reifies s W)
    => BVar s (t a)
    -> BVar s a
stdevModel = sqrt . varModel

rangeModel
    :: (Backprop (t a), Foldable t, Functor t, Ord a, Num a, Reifies s W)
    => BVar s (t a)
    -> BVar s a
rangeModel = liftOp1 . op1 $ \xs ->
    let mn :& mx = F.fold ((:&) <$> F.minimum <*> F.maximum) xs
    in  case (:&) <$> mn <*> mx of
          Nothing           -> errorWithoutStackTrace "Backprop.Learn.Model.Function.range: empty range"
          Just (mn' :& mx') ->
            ( mx' - mn'
            , \d -> (\x -> if | x == mx'  -> d
                              | x == mn'  -> -d
                              | otherwise -> 0
                    ) <$> xs
            )


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
-- To use with vectors ('R'), use 'vmap''.
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
-- 'vmap'' ('eLU' 0.01) :: 'BVar' s ('R' n) -> BVar s (R n)
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
    => BVar s ((Double :& Double) :& (Double :& Double))
    -> BVar s (R n)
    -> BVar s (R n)
sreLUPFP ((tl :&& al) :&& (tr :&& ar)) = vmap (sreLU tl al tr ar)

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
    => BVar s (L n m :& L n m)
    -> BVar s (R m)
    -> BVar s (R m)
aplPFP (a :&& b) = apl a b

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
