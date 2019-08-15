{-# LANGUAGE DataKinds                            #-}
{-# LANGUAGE FlexibleContexts                     #-}
{-# LANGUAGE FlexibleInstances                    #-}
{-# LANGUAGE MultiParamTypeClasses                #-}
{-# LANGUAGE PartialTypeSignatures                #-}
{-# LANGUAGE TupleSections                        #-}
{-# LANGUAGE TypeApplications                     #-}
{-# LANGUAGE TypeOperators                        #-}
{-# LANGUAGE TypeSynonymInstances                 #-}
{-# LANGUAGE UndecidableInstances                 #-}
{-# OPTIONS_GHC -fno-warn-orphans                 #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

import           Backprop.Learn
import           Control.Monad.Trans.Maybe
import           Data.Bitraversable
import           Data.Default
import           Data.IDX
import           Data.Traversable
import           Data.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.Opto
import           Numeric.Opto.Run.Simple
import           System.Environment
import           System.FilePath
import           Text.Printf
import qualified Data.Vector.Generic                   as VG
import qualified Numeric.LinearAlgebra                 as HM
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

mnistNet :: Model _ _ (R 784) (R 10)
mnistNet = fca     @300 softMax
        <~ dropout      0.25
        <~ fca     @784 logistic

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    datadir:_  <- getArgs
    Just train <- loadMNIST (datadir </> "train-images-idx3-ubyte")
                            (datadir </> "train-labels-idx1-ubyte")
    Just test  <- loadMNIST (datadir </> "t10k-images-idx3-ubyte")
                            (datadir </> "t10k-labels-idx1-ubyte")
    putStrLn "Loaded data."
    net0 <- initParamNormal mnistNet 0.2 g

    let so = def { soTestSet   = Just test
                 , soEvaluate  = runTest
                 , soSkipSamps = 2500
                 }
        runTest chnk net = printf "Error: %.2f%%" ((1 - score) * 100)
          where
            score = testModelAll maxIxTest mnistNet (TJust net) chnk

    simpleRunner so train SOSingle def net0
      (adam def $ modelGradStoch crossEntropy noReg mnistNet g)
      g

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

