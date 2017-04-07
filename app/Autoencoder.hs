{-# LANGUAGE ApplicativeDo        #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}


-- import           Data.Type.Combinator
import           Control.Applicative
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
    let slices :: [(HM '[128], HM '[128])]
        slices = concat . getZipList $ do
          skips <- traverse (ZipList . flip drop holmes) [0..2]
          pure $ case skips of
            [l1,l2,l3] ->
              [(l2,l1),(l2,l3)]
            _ -> []
    slices' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList slices) g
    let (test,train) = splitAt (length slices `div` 50) slices'
    net0 :: Network 'FeedForward HM
              ( '[128] :~ FullyConnected )
             '[ '[32 ] :~ LogitMap
              , '[32 ] :~ FullyConnected
              , '[3  ] :~ LogitMap
              , '[3  ] :~ FullyConnected
              , '[32 ] :~ LogitMap
              , '[32 ] :~ FullyConnected
              , '[128] :~ SoftMax '[128]
              ]
             '[128] <- initDefNet g
    flip evalStateT net0 . forM_ [1..] $ \e -> do
      train' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList train) g
      liftIO $ printf "[Epoch %d]\n" (e :: Int)
      let chunkUp   = chunksOf batch train'
          numChunks = length chunkUp

      forM_ ([1..] `zip` chunkUp) $ \(b, chnk) -> StateT $ \n0 -> do
        printf "(Epoch %d, Batch %d / %d)\n" e (b :: Int) numChunks

        t0 <- getCurrentTime
        n' <- evaluate $ optimizeListBatches_ (bimap only_ only_ <$> chnk) n0
                                       -- (sgdOptimizer rate netOpPure crossEntropy)
                                       (batching (adamOptimizer def netOpPure crossEntropy))
                                       25
        t1 <- getCurrentTime
        printf "Trained on %d points in %s.\n" batch (show (t1 `diffUTCTime` t0))

        let encoder :: Network 'FeedForward HM ( '[128] :~ FullyConnected )
                         '[ '[32] :~ LogitMap, '[32] :~ FullyConnected, '[3] :~ LogitMap ]
                         '[3]
            encoder = takeNet known n'

        forM_ [0..127] $ \(c :: ASCII) -> do
          let enc :: HM '[3]
              enc = runNetPure encoder (oneHot (c :< Ø))
              [x,y,z] = toList $ textract enc
          printf "%s\t%.4f\t%.4f\t%.4f\n" (show (toChar c)) x y z

        let trainScore = testNetList maxTest (someNet n') chnk
            testScore  = testNetList maxTest (someNet n') test
        printf "Training Score:   %.2f%%\n" ((1 - trainScore) * 100)
        printf "Validation Score: %.2f%%\n" ((1 - testScore ) * 100)

        return ((), n')
  where
    rate :: Double
    rate  = 0.02
    batch :: Int
    batch = 10000


