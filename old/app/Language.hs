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
    -- let slices_ :: [(Vec N4 (HM '[128]), HM '[128])]
        -- slices_ = slidingPartsLast known . asFeedback $ holmes
    let slices_ :: [(Vec N8 (HM '[128]), Vec N8 (HM '[128]))]
        slices_ = slidingPartsSplit known . asFeedback $ holmes
    slices <- evaluate . force $ slices_
    putStrLn "Processed data"
    let opt0 = batching $ adamOptimizer def (netOpRecurrent_ known)
                            (sumLossDecay crossEntropy known α)
    -- net0 :: Network 'Recurrent HM ( '[128] :~ FullyConnectedR' 'MF_Logit )
    --                              '[ '[64 ] :~ ReLUMap
    --                               , '[64 ] :~ FullyConnectedR' 'MF_Logit
    --                               , '[32 ] :~ ReLUMap
    --                               , '[32 ] :~ FullyConnected
    --                               , '[128] :~ SoftMax '[128]
    --                               ]
    --                               '[128] <- initDefNet g
    net0 :: Network 'Recurrent HM ( '[128] :~ LSTM )
                                 '[ '[96 ] :~ ReLUMap
                                  , '[96 ] :~ LSTM
                                  , '[64 ] :~ ReLUMap
                                  , '[64 ] :~ FullyConnected
                                  , '[128] :~ SoftMax '[128]
                                  ]
                                  '[128] <- initDefNet g
    flip evalStateT (net0, opt0) . forM_ [1..] $ \e -> do
      train' <- liftIO . fmap V.toList $ MWC.uniformShuffle (V.fromList slices) g
      liftIO $ printf "[Epoch %d]\n" (e :: Int)

      let chunkUp   = chunksOf batch train'
          numChunks = length chunkUp
      forM_ ([1..] `zip` chunkUp) $ \(b, chnk) -> StateT $ \(n0, o0) -> do
        printf "(Epoch %d, Batch %d / %d)\n" (e :: Int) (b :: Int) numChunks

        t0 <- getCurrentTime
        -- n' <- evaluate $ optimizeList_ (bimap vecToProd only_ <$> chnk) n0
        (n', o') <- evaluate
          $ optimizeListBatches (bimap vecToProd vecToProd <$> chnk) n0 o0 25
        t1 <- getCurrentTime
        printf "Trained on %d points in %s.\n" batch (show (t1 `diffUTCTime` t0))

        forM_ (map (bimap toList (last . toList)) . take 3 $ chnk) $ \(lastChnk, x0) -> do
          let (ys, primed)   = runNetRecurrent n' lastChnk
              next :: HM '[128] -> IO ((Char, HM '[128]), HM '[128])
              next x = do
                pick <- pickNext 4 x g
                return ((toChar pick, x), oneHot (only pick))
          test <- toList . fst
              <$> runNetFeedbackM (known @_ @_ @(N10 + N6)) next primed x0

          forM_ (zip (lastChnk ++ [x0]) (ys ++ [snd (head test)])) $ \(c,y) ->
            printf "|%c\t=> %s\t(%.4f)\n"
              (censor (oneHotChar c))
              (take 25 (censor <$> charRank y))
              (amax y)
          forM_ (zip test (drop 1 test)) $ \((t,_),(_,p)) ->
            printf " %c\t=> %s\t(%.4f)\n"
              (censor t)
              (take 25 (censor <$> charRank p))
              (amax p)
          putStrLn "---"

        let (test, _) = runNetRecurrentLast n' . vecNonEmpty . fst . head $ chnk
        let n'' | isNaN (amax test) = n0
                | otherwise         = n'
        return ((), (n'', o'))
  where
    batch :: Int
    batch = 1000
    α :: Double
    α = 2/3

pickNext
    :: (PrimMonad m, BLAS t, KnownNat n)
    => Double
    -> t '[n]
    -> MWC.Gen (PrimState m)
    -> m (Finite n)
pickNext α x g
    = fmap fromIntegral
    . flip MWC.categorical g
    . fmap ((** α) . realToFrac)
    . VSi.fromSized
    . textract
    $ x


censor :: Char -> Char
censor c
    | isPrint c = c
    | otherwise = '░'

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
