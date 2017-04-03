{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ViewPatterns         #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import           Control.DeepSeq
import           Control.Exception
import           Control.Monad.IO.Class
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Char
import           Data.Finite
import           Data.Foldable
import           Data.List
import           Data.List.Split
import           Data.Maybe
import           Data.Ord
import           Data.Time.Clock
import           Data.Type.Combinator
import           Data.Type.Product hiding                    (toList)
import           Data.Type.Vector
import           Learn.Neural
import           Learn.Neural.Layer.Recurrent.FullyConnected
import           Numeric.BLAS.HMatrix
import           Numeric.Backprop.Op
import           Text.Printf hiding                          (toChar, fromChar)
import           Type.Class.Known
import           Type.Family.Nat
import qualified Data.List.NonEmpty                          as NE
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
    let slices_ :: [(Vec N8 (HM '[128]), HM '[128])]
        slices_ = slidingPartsLast known . asFeedback $ holmes
    slices <- evaluate . force $ slices_
    putStrLn "Processed data"
    net0 :: Network 'Recurrent HM ( '[128] :~ FullyConnectedR' 'MF_Logit )
                                 '[ '[192] :~ ReLUMap
                                  -- , '[64 ] :~ FullyConnectedR' 'MF_Logit
                                  -- , '[32 ] :~ ReLUMap
                                  , '[192] :~ FullyConnected
                                  , '[128] :~ SoftMax '[128]
                                  ]
                                  '[128] <- initDefNet g
    flip evalStateT net0 . forM_ [1..] $ \e -> do
      train' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList slices) g
      liftIO $ printf "[Epoch %d]\n" (e :: Int)

      let chunkUp   = chunksOf batch train'
          numChunks = length chunkUp
      forM_ ([1..] `zip` chunkUp) $ \(b, chnk) -> StateT $ \n0 -> do
        printf "(Batch %d / %d)\n" (b :: Int) numChunks

        t0 <- getCurrentTime
        n' <- evaluate $ optimizeList_ (bimap vecToProd only_ <$> chnk) n0
                           (sgdOptimizer rate (netOpRecurrentLast_ known) crossEntropy)
        t1 <- getCurrentTime
        printf "Trained on %d points in %s.\n" batch (show (t1 `diffUTCTime` t0))

        let (lastChnk, x0) = first toList $ last chnk
            (ys, primed) = runNetRecurrent n' lastChnk
            test = runNetFeedbackForever id primed x0

        forM_ (zip lastChnk ys) $ \(c,y) -> do
          putStrLn $ oneHotChar c : "\t=> " ++ take 25 (filter isPrint (charRank y))
        forM_ (take 15 test) $ \(filter isPrint.charRank->(z:zs)) -> do
          putStrLn $ z : "\t<| " ++ take 25 zs
        -- let (x1,_) = runNet primed x0
        -- print $ iamax x1
        -- print $ tindex (only (iamax x1)) x1
        -- putStrLn
        --   $ map oneHotChar (toList lastChnk) ++
        --       '|' : map oneHotChar test

        return ((), n')
  where
    batch :: Int
    batch = 1000
    rate :: Double
    rate  = 0.1

instance NFData a => NFData (I a) where
    rnf = \case
      I x -> rnf x

instance NFData (f a) => NFData (VecT n f a) where
    rnf = \case
      ØV -> ()
      x :* xs -> x `deepseq` rnf xs

vecToProd
    :: VecT n f a
    -> Prod f (Replicate n a)
vecToProd = \case
    ØV      -> Ø
    x :* xs -> x :< vecToProd xs

vecNonEmpty
    :: Vec ('S n) a
    -> NE.NonEmpty a
vecNonEmpty = \case
    I x :* xs -> x NE.:| toList xs
