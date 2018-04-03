{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

import           Backprop.Learn.Loss
import           Backprop.Learn.Model
import           Backprop.Learn.Model.Combinator
import           Backprop.Learn.Model.Function
import           Backprop.Learn.Model.Neural
import           Backprop.Learn.Train
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
import           Data.Foldable
import           Data.IDX
import           Data.Primitive.MutVar
import           Data.Time
import           Data.Traversable
import           Data.Tuple
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.Opto
import           Numeric.Opto.Ref
import           Statistics.Distribution.Normal
import           System.Environment
import           System.FilePath
import           Text.Printf
import qualified Data.Conduit.Combinators              as C
import qualified Data.Text                             as T
import qualified Data.Vector.Generic                   as VG
import qualified Numeric.LinearAlgebra                 as HM
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

instance (Additive a , Additive b ) => Additive (T2 a b) where
    (.+.)   = gAdd
    addZero = gAddZero
instance (Scaling c a, Scaling c b) => Scaling c (T2 a b)
instance (Metric c a , Metric c b, Ord c, Floating c) => Metric c (T2 a b)
instance (Additive a, Additive b, Ref m (T2 a b) v) => AdditiveInPlace m v (T2 a b)
instance (Scaling c a, Scaling c b, Ref m (T2 a b) v) => ScalingInPlace m v c (T2 a b)

type MNISTNet = FCA 784 250 :.~ FCA 250 10

mnistNet :: MNISTNet
mnistNet = fca (normalDistr 0 0.2) logistic
       :.~ fca (normalDistr 0 0.2) softMax

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    datadir:_  <- getArgs
    Just train <- loadMNIST (datadir </> "train-images-idx3-ubyte")
                            (datadir </> "train-labels-idx1-ubyte")
    Just test  <- loadMNIST (datadir </> "t10k-images-idx3-ubyte")
                            (datadir </> "t10k-labels-idx1-ubyte")
    putStrLn "Loaded data."
    net0 <- fromJ_ $ initParam mnistNet g

    let report n b = do
          yield $ printf "(Batch %d)\n" (b :: Int)
          t0 <- liftIO getCurrentTime
          C.drop (n - 1)
          net' <- mapM (liftIO . evaluate . force) =<< await
          t1 <- liftIO getCurrentTime
          case net' of
            Nothing  -> yield "Done!\n"
            Just net -> do
              chnk <- lift . state $ (,[])
              yield $ printf "Trained on %d points in %s.\n"
                             (length chnk)
                             (show (t1 `diffUTCTime` t0))
              let trainScore = testNet chnk net
                  testScore  = testNet test net
              yield $ printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
              yield $ printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)

    flip evalStateT []
        . runConduit
        $ forM_ [0..] (\e -> liftIO (printf "[Epoch %d]\n" (e :: Int))
                          >> C.yieldMany train .| shuffling g
                      )
       .| C.iterM (modify . (:))      -- add to state stack for train eval
       .| void ( runOptoConduit
                   (RO' Nothing Nothing)
                   net0
                   (adam @_ @(MutVar _ (LParam MNISTNet)) def
                     (learnGradStoch crossEntropy mnistNet g)
                   )
               )
       .| mapM_ (report 2500) [0..]
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

testNet :: [(R 784, R 10)] -> LParam MNISTNet -> Double
testNet = undefined
-- testNet xs n = sum (map (uncurry test) xs) / fromIntegral (length xs)
--   where
--     test x (H.extract->t)
--         | HM.maxIndex t == HM.maxIndex (H.extract r) = 1
--         | otherwise                                  = 0
--       where
--         r = evalBP (`runNet` constVar x) n

