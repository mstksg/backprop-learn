{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}

import           Control.Monad.Trans.Maybe
import           Data.Bitraversable
import           Data.IDX
import           Data.Traversable
import           Data.Tuple
import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model
import           Backprop.Learn.Model.Neural
import           Backprop.Learn.Model.Function
import           Numeric.LinearAlgebra.Static.Backprop
import qualified Data.Vector.Generic                   as VG
import qualified Numeric.LinearAlgebra                 as HM
import qualified Numeric.LinearAlgebra.Static          as H

main :: IO ()
main = putStrLn "hi!"

loadMNIST
    :: FilePath
    -> FilePath
    -> IO (Maybe [(R 784, R 10)])
loadMNIST fpI fpL = runMaybeT $ do
    i <- MaybeT          $ decodeIDXFile       fpI
    l <- MaybeT          $ decodeIDXLabelsFile fpL
    d <- MaybeT . return $ labeledIntData l i
    MaybeT . return $ for d (bitraverse mkImage mkLabel . swap)
  where
    mkImage = H.create . VG.convert . VG.map (\i -> fromIntegral i / 255)
    mkLabel n = H.create $ HM.build 10 (\i -> if round i == n then 1 else 0)

