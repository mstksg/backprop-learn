{-# LANGUAGE ApplicativeDo                            #-}
{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE EmptyCase                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE PartialTypeSignatures                    #-}
{-# LANGUAGE QuantifiedConstraints                    #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TupleSections                            #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeInType                               #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE ViewPatterns                             #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures     #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Extra.Solver    #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.KnownNat.Solver #-}

import           Backprop.Learn
import           Control.Applicative
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Primitive
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.State
import           Data.Char
import           Data.Conduit
import           Data.Default
import           Data.Kind
import           Data.Proxy
import           Data.Singletons
import           Data.Singletons.TypeLits
import           Data.Time
import           Data.Type.Equality
import           Data.Type.Tuple
import           GHC.TypeLits.Compare
import           GHC.TypeNats
import           Numeric.LinearAlgebra.Static.Backprop hiding ((<>))
import           Numeric.Natural
import           Numeric.Opto
import           Options.Applicative
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import           Text.Printf
import qualified Data.Conduit.Combinators                     as C
import qualified Data.Vector.Sized                            as SV
import qualified System.Random.MWC                            as MWC

data Mode = CSimulate (Maybe Int)
          | forall s p. ( Floating s
                        , Floating p
                        , NFData s
                        , NFData p
                        , Metric Double s
                        , Metric Double p
                        , Show s
                        , Show p
                        , Initialize p
                        , Initialize s
                        , Backprop p
                        , Backprop s
                        , forall m. PrimMonad m => LinearInPlace m Double p
                        , forall m. PrimMonad m => LinearInPlace m Double s
                        )
                        => CLearn (ModelPick p s)

data ModelPick :: Type -> Type -> Type where
    MARIMA :: Sing p -> Sing d -> Sing q
           -> ModelPick (ARIMAp p q) (ARIMAs p d q)
    MFCRNN :: Sing h
           -> ModelPick (LRp h 1 :# LRp (1 + h) h) (R h)
    MLSTM  :: Sing h
           -> ModelPick (LRp h 1 :# LSTMp 1 h)     (R h :# R h)
    MGRU   :: Sing h
           -> ModelPick (LRp h 1 :# GRUp 1 h)      (R h)

data Process = PSin

modelLearn :: ModelPick p s -> Model ('Just p) ('Just s) Double Double
modelLearn = \case
    MARIMA (SNat :: Sing pp) (SNat :: Sing d) (SNat :: Sing q) ->
              arima @pp @d @q
    MFCRNN (SNat :: Sing h) ->
              funcD sumElements
           <~ fc
           <~ fcra logistic logistic
           <~ funcD konst
    MLSTM  (SNat :: Sing h) ->
              funcD sumElements
           <~ fc
           <~ lstm
           <~ funcD konst
    MGRU   (SNat :: Sing h) ->
              funcD sumElements
           <~ fc
           <~ gru
           <~ funcD konst

data Options = O { oMode     :: Mode
                 , oProcess  :: Process
                 , oNoise    :: Double
                 , oInterval :: Int
                 , oLookback :: Natural
                 }

processConduit
    :: PrimMonad m
    => Process
    -> MWC.Gen (PrimState m)
    -> ConduitT i Double m ()
processConduit = \case
    PSin -> \g -> void . flip (foldr (>=>) pure) (0, 1) . repeat $ \(t, v) -> do
      dv <- genContVar (normalDistr 0 0.025) g
      let v' = min 2 . max 0.5 $ v + dv
          t' = t + v'
      yield (sin (2 * pi * (1/25) * t))
      return (t', v')

noisyConduit
    :: PrimMonad m
    => Double
    -> MWC.Gen (PrimState m)
    -> ConduitT Double Double m ()
noisyConduit σ g = C.mapM $ \x ->
    (x + ) <$> genContVar (normalDistr 0 σ) g

-- type Context = ConduitT (Vector)

main :: IO ()
main = MWC.withSystemRandom @IO $ \g -> do
    O{..} <- execParser $ info (parseOpt <**> helper)
                            ( fullDesc
                           <> progDesc "Learning ARIMA"
                           <> header "backprop-learn-arima - backprop-learn demo"
                            )

    SomeNat (Proxy :: Proxy n) <- pure $ someNatVal oLookback
    Just Refl <- pure $ Proxy @1 `isLE` Proxy @n
    let generator = processConduit oProcess g
                 .| noisyConduit oNoise g

    case oMode of
      CSimulate lim ->
        runConduit $ generator
                  .| maybe (C.map id) C.take lim
                  .| C.mapM_ print
                  .| C.sinkNull

      CLearn (modelLearn->model) -> do
        let unrolled = trainState . unrollFinal @(SV.Vector n) $ model
        p0 <- initParamNormal unrolled 0.2 g

        let report n b = do
              liftIO $ printf "(Batch %d)\n" (b :: Int)
              t0 <- liftIO getCurrentTime
              C.drop (n - 1)
              mp <- mapM (liftIO . evaluate . force) =<< await
              t1 <- liftIO getCurrentTime
              case mp of
                Nothing -> liftIO $ putStrLn "Done!"
                Just p -> do
                  chnk <- lift . state $ (,[])
                  liftIO $ do
                    printf "Trained on %d points in %s.\n"
                      (length chnk)
                      (show (t1 `diffUTCTime` t0))
                    let trainScore = testModelAll absErrorTest unrolled (TJust p) chnk
                    printf "Training error:   %.8f\n" trainScore
                  report n (b + 1)

        flip evalStateT []
            . runConduit
            $ transPipe lift generator
           .| leadings
           .| skipSampling 0.05 g
           .| C.iterM (modify . (:))
           .| optoConduit def p0
                (adam def (modelGrad squaredError noReg unrolled))
           .| report oInterval 0
           .| C.sinkNull

parseOpt :: Parser Options
parseOpt = O <$> subparser ( command "simulate" (info (parseSim   <**> helper) (progDesc "Simulate ARIMA only"))
                          <> command "learn"    (info (parseLearn <**> helper) (progDesc "Simulate and learn model"))
                           )
             <*> option (maybeReader parseProcess)
                   ( long "process"
                  <> help "Process to learn"
                  <> showDefaultWith showProcess
                  <> value PSin
                  <> metavar "PROCESS"
                   )
             <*> option auto
                   ( short 'e'
                  <> help "Standard deviation of noise term"
                  <> showDefault
                  <> value 0.05
                  <> metavar "DOUBLE"
                   )
             <*> option auto
                   ( long "interval"
                  <> short 'i'
                  <> help "Report interval"
                  <> showDefault
                  <> value 5000
                  <> metavar "INT"
                   )
             <*> option auto
                   ( long "lookback"
                  <> short 'l'
                  <> help "Learn lookback"
                  <> showDefault
                  <> value 10
                  <> metavar "INT"
                   )
  where
    parseSim :: Parser Mode
    parseSim = CSimulate <$> optional (option auto
                                          ( short 'n'
                                         <> help "Number of items to generate (infinite, if none given)"
                                         <> metavar "INT"
                                          )
                                      )
    parseLearn :: Parser Mode
    parseLearn = subparser
        ( command "arima" (info parseARIMA (progDesc "Learn ARIMA(p,d,q) model"))
       <> command "fcrnn" (info parseFCRNN (progDesc "Learn Fully Connected RNN model"))
       <> command "lstm"  (info parseLSTM  (progDesc "Learn LSTM model"))
       <> command "gru"   (info parseGRU   (progDesc "Learn GRU model"))
        )
    parseARIMA :: Parser Mode
    parseARIMA = do
        p <- argument auto ( help "AR(p): Autoregressive lookback"
                          <> metavar "INT"
                           )
        d <- argument auto ( help "I(d): Differencing degree"
                          <> metavar "INT"
                           )
        q <- argument auto ( help "MA(q): Moving average lookback"
                          <> metavar "INT"
                           )
        pure $ withSomeSing @Nat p $ \sp@SNat ->
          withSomeSing @Nat d $ \sd@SNat ->
          withSomeSing @Nat q $ \sq@SNat ->
            CLearn (MARIMA sp sd sq)
    parseFCRNN :: Parser Mode
    parseFCRNN = do
        h <- argument auto ( help "Hidden layer size"
                          <> metavar "INT"
                          <> showDefault
                          <> value 10
                           )
        pure $ withSomeSing @Nat h $ \sh@SNat ->
          CLearn (MFCRNN sh)
    parseLSTM :: Parser Mode
    parseLSTM = do
        h <- argument auto ( help "Hidden layer size"
                          <> metavar "INT"
                          <> showDefault
                          <> value 10
                           )
        pure $ withSomeSing @Nat h $ \sh@SNat ->
          CLearn (MLSTM sh)
    parseGRU :: Parser Mode
    parseGRU = do
        h <- argument auto ( help "Hidden layer size"
                          <> metavar "INT"
                          <> showDefault
                          <> value 10
                           )
        pure $ withSomeSing @Nat h $ \sh@SNat ->
          CLearn (MGRU sh)

showProcess :: Process -> String
showProcess PSin = "sin"

parseProcess :: String -> Maybe Process
parseProcess s = case map toLower s of
    "sin" -> Just PSin
    _     -> Nothing

