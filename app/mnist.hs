{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

import           Backprop.Learn
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

type MNISTNet = FCA 784 300 :.~ DO 300 :.~ FCA 300 10

mnistNet :: MNISTNet
mnistNet = FCA logistic
       :.~ DO 0.25
       :.~ FCA softMax

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    datadir:_  <- getArgs
    Just train <- loadMNIST (datadir </> "train-images-idx3-ubyte")
                            (datadir </> "train-labels-idx1-ubyte")
    Just test  <- loadMNIST (datadir </> "t10k-images-idx3-ubyte")
                            (datadir </> "t10k-labels-idx1-ubyte")
    putStrLn "Loaded data."
    net0 <- initParamNormal [mnistNet] 0.2 g

    let report n b = do
          liftIO $ printf "(Batch %d)\n" (b :: Int)
          t0 <- liftIO getCurrentTime
          C.drop (n - 1)
          net' <- mapM (liftIO . evaluate . force) =<< await
          t1 <- liftIO getCurrentTime
          case net' of
            Nothing  -> liftIO $ putStrLn "Done!"
            Just net -> do
              chnk <- lift . state $ (,[])
              liftIO $ do
                printf "Trained on %d points in %s.\n"
                  (length chnk)
                  (show (t1 `diffUTCTime` t0))
                let trainScore = testLearnAll maxIxTest mnistNet (J_I net) chnk
                    testScore  = testLearnAll maxIxTest mnistNet (J_I net) test
                printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
                printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)

    flip evalStateT []
        . runConduit
        $ forM_ [0..] (\e -> liftIO (printf "[Epoch %d]\n" (e :: Int))
                          >> C.yieldMany train .| shuffling g
                      )
       .| C.iterM (modify . (:))      -- add to state stack for train eval
       .| runOptoConduit_
            (RO' Nothing Nothing)
            net0
            (adam @_ @(MutVar _ (LParam MNISTNet)) def
              (learnGradStoch crossEntropy noReg mnistNet g)
            )
       .| mapM_ (report 2500) [0..]
       .| C.sinkNull

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

