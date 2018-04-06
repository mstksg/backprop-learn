{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE FlexibleContexts                         #-}
{-# LANGUAGE GADTs                                    #-}
{-# LANGUAGE KindSignatures                           #-}
{-# LANGUAGE LambdaCase                               #-}
{-# LANGUAGE RankNTypes                               #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TupleSections                            #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeOperators                            #-}
{-# LANGUAGE ViewPatterns                             #-}
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
import           Data.Conduit
import           Data.Default
import           Data.Kind
import           Data.Primitive.MutVar
import           Data.Proxy
import           Data.Time
import           Data.Type.Equality
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
import qualified System.Random.MWC                            as MWC

data Mode = CSimulate (Maybe Int)
          | forall l s p. ( Learn Double Double l
                          , LStateMaybe l ~ 'Just s
                          , LParamMaybe l ~ 'Just p
                          , Floating s
                          , Floating p
                          , NFData s
                          , NFData p
                          , Metric Double s
                          , Metric Double p
                          , Show s
                          , Show p
                          )
                          => CLearn (Model l)
              -- (forall n. KnownNat n => LearnFunc ('Just p) 'Nothing (SV.Vector n Double) Double)

data Model :: Type -> Type where
    MARMA  :: (KnownNat p, KnownNat q) => Model (ARMA p q)
    MFCRNN :: Model (Dimap (R 1) (R 1) Double Double (FCRA 3 1 3 :.~ FCA 3 1))

modelLearn :: Model t -> t
modelLearn = \case
    MARMA  -> armaSim
    MFCRNN -> DM { _dmPre   = konst
                 , _dmPost  = sumElements
                 , _dmLearn = fcra (normalDistr 0 0.2) (normalDistr 0 0.2) logistic logistic
                          :.~ fca (normalDistr 0 0.2) id
                 }

data Options = O { oMode     :: Mode
                 , oP        :: Natural
                 , oQ        :: Natural
                 , oNoise    :: Double
                 , oInterval :: Int
                 , oLookback :: Natural
                 }

armaSim :: (KnownNat p, KnownNat q) => ARMA p q
armaSim = ARMA { _armaGenPhi   = \g i ->
                    (/ (fromIntegral i + 5)) <$> genContVar (normalDistr 0 1) g
               , _armaGenTheta = \g i ->
                    (/ (fromIntegral i + 5)) <$> genContVar (normalDistr 0 1) g
               , _armaGenConst = genContVar $ normalDistr 0 10
               , _armaGenYHist = genContVar $ normalDistr 0 0.2
               , _armaGenEHist = genContVar $ normalDistr 0 0.2
               }

genSim
    :: forall p q m i. (KnownNat p, KnownNat q, PrimMonad m)
    => ARMA p q
    -> Double
    -> MWC.Gen (PrimState m)
    -> ConduitT i Double m ()
genSim sim σ g = do
    p  <- fromJ_ $ initParam noisySim g
    s0 <- fromJ_ $ initState noisySim g
    void . foldr (>=>) pure (repeat (go p)) $ (0, J_I s0)
  where
    noisySim = sim :.~ injectNoise (normalDistr 0 σ)
    go  :: ARMAp p q
        -> (Double, Mayb I ('Just (ARMAs p q)))
        -> ConduitT i Double m (Double, Mayb I ('Just (ARMAs p q)))
    go p (y, s) = do
      ys@(y', _) <- lift $ runLearnStoch_ noisySim g (J_I p) y s
      ys <$ yield y'

main :: IO ()
main = MWC.withSystemRandom @IO $ \g -> do
    O{..} <- execParser $ info (parseOpt <**> helper)
                            ( fullDesc
                           <> progDesc "Learning ARMA"
                           <> header "backprop-learn-arma - backprop-learn demo"
                            )

    SomeNat (Proxy :: Proxy p) <- pure $ someNatVal oP
    SomeNat (Proxy :: Proxy q) <- pure $ someNatVal oQ
    SomeNat (Proxy :: Proxy n) <- pure $ someNatVal oLookback
    Just Refl <- pure $ Proxy @1 `isLE` Proxy @n
    let armaSim'  = armaSim @p @q

    case oMode of
      CSimulate lim -> do
        runConduit $ genSim armaSim' oNoise g
                  .| maybe (C.map id) C.take lim
                  .| C.mapM_ print
                  .| C.sinkNull

      CLearn (modelLearn->model) -> do
        let unrolled = UnrollFinalTrainState @_ @n model
        p0 <- fromJ_ $ initParam unrolled g
        -- print p0

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
                    let trainScore = testLearnAll squaredErrorTest unrolled (J_I p) chnk
                    printf "Training error:   %.8f\n" trainScore
                    -- let e = norm_2 (p0' - p')
                    -- printf "Error: %0.6f\n" e
                  report n (b + 1)

        flip evalStateT []
            . runConduit
            $ genSim armaSim' oNoise g
           .| leadings
           .| skipSampling 0.02 g
           .| C.iterM (modify . (:))
           .| runOptoConduit_
                (RO' Nothing Nothing)
                p0
                (adam @_ @(MutVar _ _) def
                   (learnGrad squaredError unrolled)
                )
           .| report oInterval 0
           .| C.sinkNull

parseOpt :: Parser Options
parseOpt = O <$> subparser ( command "simulate" (info (parseSim   <**> helper) (progDesc "Simulate ARMA only"))
                          <> command "learn"    (info (parseLearn <**> helper) (progDesc "Simulate and learn model"))
                           )
             <*> option auto
                   ( short 'p'
                  <> help "AR(p): Autoregressive degree"
                  <> showDefault
                  <> value 3
                  <> metavar "INT"
                   )
             <*> option auto
                   ( short 'q'
                  <> help "MA(q): Moving average degree"
                  <> showDefault
                  <> value 3
                  <> metavar "INT"
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
                  <> value 3
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
        ( command "arma"  (info (pure (CLearn (MARMA @3 @3))) (progDesc "Learn ARMA model"))
       <> command "fcrnn" (info (pure (CLearn MFCRNN)) (progDesc "Learn Fully Connected RNN model"))
        )
