{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Default
import           Data.Finite
import           Data.IDX
import           Data.List.Split
import           Data.Time.Clock
import           Data.Traversable
import           Data.Tuple
import           Data.Type.Product
import           Learn.Neural
import           Numeric.BLAS.HMatrix
import           Numeric.LinearAlgebra.Static
import           Text.Printf
import qualified Data.Vector                     as V
import qualified Data.Vector.Generic             as VG
import qualified Data.Vector.Unboxed             as VU
import qualified System.Random.MWC               as MWC
import qualified System.Random.MWC.Distributions as MWC

loadMNIST
    :: FilePath
    -> FilePath
    -> IO (Maybe [(HM '[784], HM '[10])])
loadMNIST fpI fpL = runMaybeT $ do
    i <- MaybeT          $ decodeIDXFile       fpI
    l <- MaybeT          $ decodeIDXLabelsFile fpL
    d <- MaybeT . return $ labeledIntData l i
    r <- MaybeT . return $ for d (bitraverse mkImage mkLabel . swap)
    liftIO . evaluate $ force r
  where
    mkImage :: VU.Vector Int -> Maybe (HM '[784])
    mkImage = fmap HM . create . VG.convert . VG.map (\i -> fromIntegral i / 255)
    mkLabel :: Int -> Maybe (HM '[10])
    mkLabel = fmap (oneHot . only) . packFinite . fromIntegral

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    Just train <- loadMNIST "data/train-images-idx3-ubyte" "data/train-labels-idx1-ubyte"
    Just test  <- loadMNIST "data/t10k-images-idx3-ubyte"  "data/t10k-labels-idx1-ubyte"
    putStrLn "Loaded data."
    net0 :: Network 'FeedForward HM ( '[784] :~ FullyConnected )
                                   '[ '[300] :~ LogitMap
                                    , '[300] :~ FullyConnected
                                    , '[100] :~ LogitMap
                                    , '[100] :~ FullyConnected
                                    , '[10 ] :~ SoftMax '[10]
                                    ]
                                    '[10] <- initDefNet g
    let dout = alongNet net0 $ Nothing
                           :&% Just 0.2
                           :&% Nothing
                           :&% Just 0.2
                           :&% Nothing
                           :&% DOExt
    flip evalStateT net0 . forM_ [1..] $ \e -> do
      train' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList train) g
      liftIO $ printf "[Epoch %d]\n" (e :: Int)

      forM_ ([1..] `zip` chunksOf batch train') $ \(b, chnk) -> StateT $ \n0 -> do
        printf "(Batch %d)\n" (b :: Int)

        t0 <- getCurrentTime
        -- n' <- evaluate $ optimizeList_ (bimap only_ only_ <$> chnk) n0
        --                                -- (sgdOptimizer rate netOpPure crossEntropy)
        --                                (adamOptimizer def netOpPure crossEntropy)
        n' <- optimizeListM_ (bimap only_ only_ <$> chnk) n0
                             (adamOptimizerM def (netOpDOPure dout g) crossEntropy)
        t1 <- getCurrentTime
        printf "Trained on %d points in %s.\n" batch (show (t1 `diffUTCTime` t0))

        let trainScore = testNetList maxTest (someNet n') chnk
            testScore  = testNetList maxTest (someNet n') test
        printf "Training error:   %.2f%%\n" ((1 - trainScore) * 100)
        printf "Validation error: %.2f%%\n" ((1 - testScore ) * 100)

        return ((), n')
  where
    -- rate :: Double
    -- rate  = 0.02
    batch :: Int
    batch = 2500
