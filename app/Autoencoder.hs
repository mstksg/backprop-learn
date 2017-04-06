{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- import           Data.Type.Combinator
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad.IO.Class
import           Control.Monad.Primitive
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Char
import           Data.Default
import           Data.Finite
import           Data.Foldable
import           Data.List
import           Data.List.Split
import           Data.Maybe
import           Data.Ord
import           Data.Singletons
import           Data.Time.Clock
import           Data.Type.Product hiding                    (toList, head')
import           Data.Type.Vector
import           GHC.TypeLits hiding                         (type (+))
import           Learn.Neural
import           Learn.Neural.Layer.Recurrent.FullyConnected
import           Learn.Neural.Layer.Recurrent.LSTM
import           Numeric.BLAS.HMatrix
import           Numeric.Backprop.Op hiding                  (head')
import           Text.Printf hiding                          (toChar, fromChar)
import           Type.Class.Known
import           Type.Family.Nat
import qualified Data.List.NonEmpty                          as NE
import qualified Data.Type.Nat                               as TCN
import qualified Data.Vector                                 as V
import qualified Data.Vector.Sized                           as VSi
import qualified System.Random.MWC                           as MWC
import qualified System.Random.MWC.Distributions             as MWC


type ASCII = Finite 128

fromChar :: Char -> Maybe ASCII
fromChar = packFinite . fromIntegral . ord

toChar :: ASCII -> Char
toChar = chr . fromIntegral

charOneHot :: Tensor t => Char -> Maybe (t '[128])
charOneHot = fmap (oneHot . only) . fromChar

oneHotChar :: BLAS t => t '[128] -> Char
oneHotChar = toChar . iamax

charRank :: Tensor t => t '[128] -> [Char]
charRank = map fst . sortBy (flip (comparing snd)) . zip ['\0'..] . toList . textract

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    holmes <- evaluate . force . mapMaybe (charOneHot @HM)
        =<< readFile "data/holmes.txt"
    putStrLn "Loaded data"
    let slices :: [(HM '[128], HM '[256])]
        slices =
          zipWith3 (\x y z -> (y, tload sing (textract x VSi.++ textract z)))
            holmes (drop 1 holmes) (drop 2 holmes)
    slices' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList slices) g
    let (test,train) = splitAt (length slices `div` 50) slices'
    -- mapM_ print slices
    net0 :: Network 'FeedForward HM
              ( '[128] :~ FullyConnected )
             '[ '[16 ] :~ LogitMap
              , '[16 ] :~ FullyConnected
              , '[2  ] :~ LogitMap
              , '[2  ] :~ FullyConnected
              , '[24 ] :~ LogitMap
              , '[24 ] :~ FullyConnected
              , '[256] :~ LogitMap
              ]
             '[256] <- initDefNet g
    flip evalStateT net0 . forM_ [1..] $ \e -> do
      train' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList train) g
      liftIO $ printf "[Epoch %d]\n" (e :: Int)
      let chunkUp   = chunksOf batch train'
          numChunks = length chunkUp

      forM_ ([1..] `zip` chunkUp) $ \(b, chnk) -> StateT $ \n0 -> do
        printf "(Epoch %d, Batch %d / %d)\n" e (b :: Int) numChunks

        t0 <- getCurrentTime
        n' <- evaluate $ optimizeList_ (bimap only_ only_ <$> chnk) n0
                                       -- (sgdOptimizer rate netOpPure crossEntropy)
                                       (adamOptimizer def netOpPure crossEntropy)
        t1 <- getCurrentTime
        printf "Trained on %d points in %s.\n" batch (show (t1 `diffUTCTime` t0))

        let trainScore = testNetList crossEntropyTest (someNet n') chnk
            testScore  = testNetList crossEntropyTest (someNet n') test
        printf "Training Log Cross Entropy:   %.2f\n" (log trainScore)
        printf "Validation Log Cross Entropy: %.2f\n" (log testScore)

        return ((), n')
  where
    rate :: Double
    rate  = 0.02
    batch :: Int
    batch = 10000


