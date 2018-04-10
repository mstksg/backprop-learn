{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TupleSections                            #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeOperators                            #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise       #-}

import           Backprop.Learn
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Data.Char
import           Data.Conduit
import           Data.Default
import           Data.Foldable
import           Data.Primitive.MutVar
import           Data.Proxy
import           Data.Time
import           Data.Type.Equality
import           GHC.TypeNats
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.LinearAlgebra.Static.Vector
import           Numeric.Opto
import           Statistics.Distribution.Normal
import           System.Environment
import           Text.Printf
import qualified Conduit                               as C
import qualified Data.Conduit.Combinators              as C
import qualified Data.Set                              as S
import qualified Data.Text                             as T
import qualified Data.Vector.Storable.Sized            as SVS
import qualified System.Random.MWC                     as MWC
import qualified System.Random.MWC.Distributions       as MWC

type CharRNN n h1 h2 = Chain '[ LSTM n h1
                              , DO h1
                              , LSTM h1 h2
                              , DO h2
                              , FCA h2 n
                              ]
                         (R n) (R n)

charRNN :: (KnownNat n, KnownNat h1, KnownNat h2) => CharRNN n h1 h2
charRNN = lstm (normalDistr 0 0.2) (normalDistr 0 0.2) (normalDistr 0 0.2) True
      :~> DO 0.25
      :~> lstm (normalDistr 0 0.2) (normalDistr 0 0.2) (normalDistr 0 0.2) True
      :~> DO 0.25
      :~> fca  (normalDistr 0 0.2) softMax
      :~> CNil

oneHotChar
    :: KnownNat n
    => S.Set Char
    -> Char
    -> R n
oneHotChar cs = oneHotR . fromIntegral . (`S.findIndex` cs)

main :: IO ()
main = MWC.withSystemRandom @IO $ \g -> do
    sourceFile:_  <- getArgs
    charMap <- S.fromList <$> readFile sourceFile
    SomeNat (Proxy :: Proxy n) <- pure $ someNatVal (fromIntegral (length charMap))
    SomeNat (Proxy :: Proxy n') <- pure $ someNatVal (fromIntegral (length charMap - 1))
    Just Refl <- pure $ sameNat (Proxy @(n' + 1)) (Proxy @n)

    printf "%d characters found.\n" (natVal (Proxy @n))

    let model0 = charRNN @n @100 @50
        model  = UnrollFinalTrainState @_ @15 model0

    p0 <- fromJ_ $ initParam model g

    let report n b = do
          liftIO $ printf "(Batch %d)\n" (b :: Int)
          t0 <- liftIO getCurrentTime
          C.drop (n - 1)
          mp <- mapM (liftIO . evaluate . force) =<< await
          t1 <- liftIO getCurrentTime
          case mp of
            Nothing -> liftIO $ putStrLn "Done!"
            Just p@(T2 p' s') -> do
              chnk <- lift . state $ (,[])
              liftIO $ do
                printf "Trained on %d points in %s.\n"
                  (length chnk)
                  (show (t1 `diffUTCTime` t0))
                let trainScore = testLearnAll maxIxTest model (J_I p) chnk
                printf "Training error:   %.3f%%\n" ((1 - trainScore) * 100)

                forM_ (take 15 chnk) $ \(x,y) -> do
                  let primed = primeLearn model0 (J_I p') x (J_I s')
                  testOut <- fmap reverse . flip execStateT [] $
                      iterateLearnM ( fmap (oneHotR . fromIntegral)
                                    . (>>= \r -> r <$ modify (r:))    -- trace
                                    . (`MWC.categorical` g)
                                    . SVS.fromSized
                                    . rVec
                                    )
                            100 model0 (J_I p') y primed
                  printf "%s|%s\n"
                    (sanitize . (`S.elemAt` charMap) . fromIntegral . maxIndexR <$> (toList x ++ [y]))
                    (sanitize . (`S.elemAt` charMap) <$> testOut)
              report n (b + 1)

    C.runResourceT . flip evalStateT []
        . runConduit
        $ forever ( C.sourceFile sourceFile
                 .| C.decodeUtf8
                 .| C.concatMap T.unpack
                 .| C.map (oneHotChar charMap)
                 .| leadings
                  )
       .| skipSampling 0.02 g
       .| C.iterM (modify . (:))
       .| runOptoConduit_
            (RO' Nothing Nothing)
            p0
            (adam @_ @(MutVar _ _) def
               (learnGradStoch crossEntropy model g)
            )
       .| report 2500 0
       .| C.sinkNull

sanitize :: Char -> Char
sanitize c | isPrint c = c
           | otherwise = '#'
