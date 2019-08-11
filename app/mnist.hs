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
import           Control.Concurrent.STM
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State
import           Data.Bitraversable
import           Data.Conduit
import           Data.Default
import           Data.IDX
import           Data.Primitive.MutVar
import           Data.Time
import           Data.Traversable
import           Data.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.Opto
import           System.Environment
import           System.FilePath
import           Text.Printf
import qualified Data.Conduit.Combinators              as C
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
    sampleQueue <- atomically $ newTBQueue 25000

    let o :: PrimMonad m => Opto m (R 784, R 10) Net
        o = adam def $
              modelGradStoch crossEntropy noReg mnistNet g

        report b = do
          yield $ printf "(Batch %d)\n" (b :: Int)
          t0   <- liftIO getCurrentTime
          _    <- liftIO . atomically $ flushTBQueue sampleQueue
          net' <- mapM (liftIO . evaluate . force) =<< await
          chnk <- liftIO . atomically $ flushTBQueue sampleQueue
          t1   <- liftIO getCurrentTime
          case net' of
            Nothing  -> yield "Done!\n"
            Just net -> do
              yield $ printf "Trained on %d points in %s.\n"
                             (length chnk)
                             (show (t1 `diffUTCTime` t0))
              let trainScore = testNet chnk net
                  testScore  = testNet test net
              yield $ printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
              yield $ printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)

    runConduit $ forM_ [0..] (\e -> liftIO (printf "[Epoch %d]\n" (e :: Int))
                                 >> C.yieldMany train .| shuffling g
                             )
              .| C.iterM (automatically . writeTBQUeue sampleQueue)
              .| optoConduit def net0 o
              .| forever (C.drop 2499 *> (mapM_ yield =<< await))
              .| mapM_ report [0..]
              .| C.map T.pack
              .| C.encodeUtf8
              .| C.stdout

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

