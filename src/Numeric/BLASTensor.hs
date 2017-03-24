{-# LANGUAGE TypeFamilies #-}

module Numeric.BLASTensor (
    BLASTensor
  , module Numeric.BLAS
  , module Numeric.Tensor
  ) where

import           Numeric.BLAS
import           Numeric.Tensor

class (BLAS b, Tensor b, ElemT b ~ Scalar b) => BLASTensor b


