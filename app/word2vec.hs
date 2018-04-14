{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}

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
import           Data.List
import           Data.Primitive.MutVar
import           Data.Proxy
import           Data.Time
import           GHC.TypeNats
import           Numeric.Backprop.Tuple
import           Numeric.LinearAlgebra.Static.Backprop
import           Numeric.Opto
import           System.Environment
import           Text.Printf
import qualified Conduit                               as C
import qualified Data.Conduit.Combinators              as C
import qualified Data.Set                              as S
import qualified Data.Text                             as T
import qualified Data.Vector.Sized                     as SV
import qualified Data.Vector.Storable                  as VS
import qualified Numeric.LinearAlgebra.Static          as H
import qualified System.Random.MWC                     as MWC

type Encoder n e = FCA n e
type Decoder n e = FCA e n

type Word2Vec n e = Encoder n e :.~ Decoder n e

encoder :: Encoder n e
encoder = FCA logistic

decoder :: KnownNat n => Decoder n e
decoder = FCA softMax

word2vec :: forall n e. KnownNat n => Word2Vec n e
word2vec = encoder :.~ decoder

oneHotWord
    :: KnownNat n
    => S.Set String
    -> String
    -> Maybe (R n)
oneHotWord ws = fmap (oneHotR . fromIntegral) . (`S.lookupIndex` ws)

makeCBOW :: KnownNat w => SV.Vector w (R n) -> (R n, R n)
makeCBOW v = (SV.index v mid, SV.sum (v SV.// [(mid, 0)]))
  where
    mid = maxBound `div` 2

main :: IO ()
main = MWC.withSystemRandom @IO $ \g -> do
    sourceFile:logFile:testFile:_  <- getArgs
    wordSet <- S.fromList . tokenize <$> readFile sourceFile
    SomeNat (Proxy :: Proxy n) <- pure $ someNatVal (fromIntegral (S.size wordSet))

    printf "%d unique words found.\n" (natVal (Proxy @n))

    let model@(enc :.~ _) = word2vec @n @100
    p0 <- initParamNormal [model] 0.2 g


    let report n b = do
          liftIO $ printf "(Batch %d)\n" (b :: Int)
          t0 <- liftIO getCurrentTime
          C.drop (n - 1)
          mp <- mapM (liftIO . evaluate . force) =<< await
          t1 <- liftIO getCurrentTime
          case mp of
            Nothing -> liftIO $ putStrLn "Done!"
            Just p@(T2 pEnc _) -> do
              chnk <- lift . state $ (,[])
              liftIO $ do
                printf "Trained on %d points in %s.\n"
                  (length chnk)
                  (show (t1 `diffUTCTime` t0))
                let trainScore = testLearnAll maxIxTest model (J_I p) chnk
                printf "Training error:   %.3f%%\n" ((1 - trainScore) * 100)

                testWords <- tokenize <$> readFile testFile
                let tests = flip map testWords $ \w ->
                       let v = maybe 0 (runLearnStateless_ enc (J_I pEnc))
                                $ oneHotWord wordSet w
                       in  intercalate "," $ map (printf "%0.4f") (VS.toList (H.extract v))

                writeFile logFile $ unlines tests

              report n (b + 1)


    C.runResourceT . flip evalStateT []
        . runConduit
        $ forever ( C.sourceFile sourceFile
                 .| C.decodeUtf8
                 .| C.concatMap (tokenize . T.unpack)
                 .| C.concatMap (oneHotWord wordSet)
                 .| C.slidingWindow 5
                 .| C.concatMap (SV.fromList @5)
                 .| C.map makeCBOW
                  )
       .| skipSampling 0.02 g
       .| C.iterM (modify . (:))
       .| runOptoConduit_
            (RO' Nothing Nothing)
            p0
            (adam @_ @(MutVar _ _) def
               (learnGradStoch crossEntropy noReg model g)
            )
       .| report 500 0
       .| C.sinkNull

tokenize :: String -> [String]
tokenize = words . map (whitePunc . toLower)
  where
    whitePunc c
      | isPunctuation c = ' '
      | otherwise       = c
