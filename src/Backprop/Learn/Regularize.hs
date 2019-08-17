{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Backprop.Learn.Regularize (
    Regularizer
  , Regularize(..)
  , l1Reg
  , l2Reg
  , noReg
  , l2RegMetric
  , l1RegMetric
  -- * Build instances
  -- ** DerivingVia
  , RegularizeMetric(..), NoRegularize(..)
  -- ** Linear
  , lassoLinear, ridgeLinear
  -- ** Generics
  , grnorm_1, grnorm_2
  , glasso, gridge
  -- * Manipulate regularizers
  , addReg
  , scaleReg
  ) where

import           Control.Applicative
import           Control.Monad.Trans.State
import           Data.Ratio
import           Data.Semigroup hiding                 (Any(..))
import           Data.Type.Functor.Product
import           Data.Type.Tuple
import           Data.Vinyl
import           GHC.Exts
import           GHC.Generics
import           GHC.TypeNats
import           Generics.OneLiner
import           Numeric.Backprop                      as B
import           Numeric.LinearAlgebra.Static.Backprop ()
import           Numeric.Opto.Update hiding            ((<.>))
import qualified Data.Functor.Contravariant            as Co
import qualified Data.Vector.Generic                   as VG
import qualified Data.Vector.Generic.Sized             as SVG
import qualified Numeric.LinearAlgebra.Static          as H

-- | A regularizer on parameters
type Regularizer p = forall s. Reifies s W => BVar s p -> BVar s Double

-- | A class for data types that support regularization during training.
--
-- This class is somewhat similar to @'Metric' 'Double'@, in that it
-- supports summing the components and summing squared components.
-- However, the main difference is that when summing components, we only
-- consider components that we want to regularize.
--
-- Often, this doesn't include bias terms (terms that "add" to inputs), and
-- only includes terms that "scale" inputs, like components in a weight
-- matrix of a feed-forward neural network layer.
--
-- However, if all of your components are to be regularized, you can use
-- 'norm_1', 'norm_2', 'lassoLinear', and 'ridgeLinear' as sensible
-- implementations, or use DerivingVia with 'RegularizeMetric':
--
-- @
-- data MyType = ...
--   deriving Regularize via (RegularizeMetric MyType)
-- @
--
-- You can also derive an instance where /no/  are regularized, using
-- 'NoRegularize':
--
-- @
-- data MyType = ...
--   deriving Regularize via (NoRegularize MyType)
-- @
--
-- The default implementations are based on 'Generics', and work for types
-- that are records of items that are all instances of 'Regularize'.
class Backprop p => Regularize p where

    -- | Like 'norm_1': sums all of the weights in @p@, but only the
    -- ones you want to regularize:
    --
    -- \[
    -- \sum_w \lvert w \rvert
    -- \]
    --
    -- Note that typically bias terms (terms that add to inputs) are not
    -- regularized.  Only "weight" terms that scale inputs are typically
    -- regularized.
    --
    -- If @p@ is an instance of 'Metric', then you can set @'rnorm_1'
    -- = 'norm_1'@.  However, this would count /all/ terms in @p@, even
    -- potential bias terms.
    rnorm_1 :: p -> Double

    default rnorm_1 :: (ADT p, Constraints p Regularize) => p -> Double
    rnorm_1 = grnorm_1

    -- | Like 'norm_2': sums all of the /squares/ of the weights
    -- n @p@, but only the ones you want to regularize:
    --
    -- \[
    -- \sum_w w^2
    -- \]
    --
    -- Note that typically bias terms (terms that add to inputs) are not
    -- regularized.  Only "weight" terms that scale inputs are typically
    -- regularized.
    --
    -- If @p@ is an instance of 'Metric', then you can set @'rnorm_2'
    -- = 'norm_2'@.  However, this would count /all/ terms in @p@, even
    -- potential bias terms.
    rnorm_2 :: p -> Double

    default rnorm_2 :: (ADT p, Constraints p Regularize) => p -> Double
    rnorm_2 = grnorm_2

    -- | @'lasso' r p@ sets all regularized components (that is, components
    -- summed by 'rnorm_1') in @p@ to be either @r@ if that component was
    -- positive, or @-r@ if that component was negative.  Behavior is not
    -- defined if the component is exactly zero, but either @r@ or @-r@ are
    -- sensible possibilities.
    --
    -- It must set all /non-regularized/ components (like bias terms, or
    -- whatever items that 'rnorm_1' ignores) to zero.
    --
    -- If @p@ is an instance of @'Linear' 'Double'@ and 'Num', then you can set
    -- @'lasso' = 'lassoLinear'@.  However, this is only valid if 'rnorm_1'
    -- counts /all/ terms in @p@, including potential bias terms.
    lasso   :: Double -> p -> p

    default lasso :: (ADT p, Constraints p Regularize) => Double -> p -> p
    lasso = glasso

    -- | @'ridge' r p@ scales all regularized components (that is,
    -- components summed by 'rnorm_2') in @p@ by @r@.
    --
    -- It must set all /non-regularized/ components (like bias terms, or
    -- whatever items that 'rnorm_2' ignores) to zero.
    --
    -- If @p@ is an instance of @'Linear' 'Double'@ and 'Num', then you can set
    -- @'ridge' = 'ridgeLinear'@.  However, this is only valid if 'rnorm_2'
    -- counts /all/ terms in @p@, including potential bias terms.
    ridge   :: Double -> p -> p

    default ridge :: (ADT p, Constraints p Regularize) => Double -> p -> p
    ridge = gridge

grnorm_1 :: (ADT p, Constraints p Regularize) => p -> Double
grnorm_1 = getSum . gfoldMap @Regularize (Sum . rnorm_1)

grnorm_2 :: (ADT p, Constraints p Regularize) => p -> Double
grnorm_2 = getSum . gfoldMap @Regularize (Sum . rnorm_2)

glasso :: (ADT p, Constraints p Regularize) => Double -> p -> p
glasso r = gmap @Regularize (lasso r)

gridge :: (ADT p, Constraints p Regularize) => Double -> p -> p
gridge r = gmap @Regularize (ridge r)

-- | Backpropagatable L1 regularization; also known as lasso
-- regularization.
--
-- \[
-- \sum_w \lvert w \rvert
-- \]
--
-- Note that typically bias terms (terms that add to inputs) are not
-- regularized.  Only "weight" terms that scale inputs are typically
-- regularized.
l1Reg :: Regularize p => Double -> Regularizer p
l1Reg λ = liftOp1 . op1 $ \x ->
    ( λ * rnorm_1 x
    , (`lasso` x) . (* λ)
    )

-- | Backpropagatable L2 regularization; also known as ridge
-- regularization.
--
-- \[
-- \sum_w w^2
-- \]
--
-- Note that typically bias terms (terms that add to inputs) are not
-- regularized.  Only "weight" terms that scale inputs are typically
-- regularized.
l2Reg :: Regularize p => Double -> Regularizer p
l2Reg λ = liftOp1 . op1 $ \x ->
    ( λ * rnorm_2 x
    , (`ridge` x) . (* λ)
    )

-- | No regularization
noReg :: Regularizer p
noReg _ = auto 0

-- | A default implementation of 'lasso' for instances of @'Linear'
-- 'Double'@ and 'Num'.  However, this is only valid if the corresponding
-- 'rnorm_1' counts /all/ terms in @p@, including potential bias terms.
lassoLinear :: (Linear Double p, Num p) => Double -> p -> p
lassoLinear r = (r .*) . signum

-- | A default implementation of 'ridge' for instances of @'Linear'
-- 'Double'@.  However, this is only valid if the corresponding
-- 'rnorm_2' counts /all/ terms in @p@, including potential bias terms.
ridgeLinear :: Linear Double p => Double -> p -> p
ridgeLinear = (.*)

-- | L2 regularization for instances of 'Metric'.  This will count
-- all terms, including any potential bias terms.
--
-- This is what 'l2Reg' would be for a type @p@ if you declare an instance
-- of 'Regularize' with @'rnorm_2' = 'norm_2'@, and @'ridge'
-- = 'ridgeLinear'@.
l2RegMetric
    :: (Metric Double p, Backprop p)
    => Double                   -- ^ scaling factor (often 0.5)
    -> Regularizer p
l2RegMetric λ = liftOp1 . op1 $ \x ->
            ( λ * quadrance x, (.* x) . (* λ))

-- | L1 regularization for instances of 'Metric'.  This will count
-- all terms, including any potential bias terms.
--
-- This is what 'l1Reg' would be for a type @p@ if you declare an instance
-- of 'Regularize' with @'rnorm_1' = 'norm_1'@, and @'lasso'
-- = 'lassoLinear'@.
l1RegMetric
    :: (Num p, Metric Double p, Backprop p)
    => Double                   -- ^ scaling factor (often 0.5)
    -> Regularizer p
l1RegMetric λ = liftOp1 . op1 $ \x ->
            ( λ * norm_1 x, (.* signum x) . (* λ)
            )

-- | Add together two regularizers
addReg :: Regularizer p -> Regularizer p -> Regularizer p
addReg f g x = f x + g x

-- | Scale a regularizer's influence
scaleReg :: Double -> Regularizer p -> Regularizer p
scaleReg λ reg = (* auto λ) . reg

-- | Newtype wrapper (meant to be used with DerivingVia) to derive an
-- instance of 'Regularize' that uses its 'Metric' instance, and
-- regularizes every component of a data type, including any potential bias
-- terms.
newtype RegularizeMetric a = RegularizeMetric a
  deriving (Show, Eq, Ord, Read, Generic, Functor, Backprop)

instance (Metric Double p, Num p, Backprop p) => Regularize (RegularizeMetric p) where
    rnorm_1 = coerce $ norm_1 @_ @p
    rnorm_2 = coerce $ norm_2 @_ @p
    lasso   = coerce $ lassoLinear @p
    ridge   = coerce $ ridgeLinear @p

-- | Newtype wrapper (meant to be used with DerivingVia) to derive an
-- instance of 'Regularize' that does not regularize any part of the type.
newtype NoRegularize a = NoRegularize a
  deriving (Show, Eq, Ord, Read, Generic, Functor, Backprop)

instance Backprop a => Regularize (NoRegularize a) where
    rnorm_1 _ = 0
    rnorm_2 _ = 0
    lasso _   = B.zero
    ridge _   = B.zero

instance Regularize Double where
    rnorm_1 = id
    rnorm_2 = (** 2)
    lasso r = (r *) . signum
    ridge   = (*)

instance Regularize Float where
    rnorm_1 = realToFrac
    rnorm_2 = (** 2) . realToFrac
    lasso r = (realToFrac r *) . signum
    ridge   = (*) . realToFrac

instance Integral a => Regularize (Ratio a) where
    rnorm_1 = realToFrac
    rnorm_2 = (** 2) . realToFrac
    lasso r = (realToFrac r *) . signum
    ridge   = (*) . realToFrac

instance Regularize () where
    rnorm_1 _ = 0
    rnorm_2 _ = 0
    lasso _ _ = ()
    ridge _ _ = ()
instance (Regularize a, Regularize b) => Regularize (a, b)
instance (Regularize a, Regularize b, Regularize c) => Regularize (a, b, c)
instance (Regularize a, Regularize b, Regularize c, Regularize d) => Regularize (a, b, c, d)
instance (Regularize a, Regularize b, Regularize c, Regularize d, Regularize e) => Regularize (a, b, c, d, e)

instance (Regularize a, Regularize b) => Regularize (a :# b)
instance Regularize a => Regularize (TF a)

instance (RPureConstrained Regularize as, ReifyConstraint Backprop TF as, RMap as, RApply as, RFoldMap as) => Regularize (Rec TF as) where
    rnorm_1 = getSum
            . rfoldMap getConst
            . rzipWith coerce (rpureConstrained @Regularize (Co.Op rnorm_1))
    rnorm_2 = getSum
            . rfoldMap getConst
            . rzipWith coerce (rpureConstrained @Regularize (Co.Op rnorm_2))
    lasso r = rzipWith coerce (rpureConstrained @Regularize (Endo (lasso r)))
    ridge r = rzipWith coerce (rpureConstrained @Regularize (Endo (ridge r)))

instance (PureProdC Maybe Backprop as, PureProdC Maybe Regularize as) => Regularize (PMaybe TF as) where
    rnorm_1 = getSum
            . foldMapProd getConst
            . zipWithProd coerce (pureProdC @_ @Regularize (Co.Op rnorm_1))
    rnorm_2 = getSum
            . foldMapProd getConst
            . zipWithProd coerce (pureProdC @_ @Regularize (Co.Op rnorm_2))
    lasso r = zipWithProd coerce (pureProdC @_ @Regularize (Endo (lasso r)))
    ridge r = zipWithProd coerce (pureProdC @_ @Regularize (Endo (ridge r)))

instance (VG.Vector v a, Regularize a, Backprop (SVG.Vector v n a)) => Regularize (SVG.Vector v n a) where
    rnorm_1 = (`execState` 0) . SVG.mapM_ (modify . (+) . rnorm_1)
    rnorm_2 = (`execState` 0) . SVG.mapM_ (modify . (+) . rnorm_2)
    lasso r = SVG.map (lasso r)
    ridge r = SVG.map (ridge r)

deriving via (RegularizeMetric (H.R n)) instance KnownNat n => Regularize (H.R n)
deriving via (RegularizeMetric (H.L n m)) instance (KnownNat n, KnownNat m) => Regularize (H.L n m)
