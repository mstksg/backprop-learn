{-# LANGUAGE DataKinds                                #-}
{-# LANGUAGE RecordWildCards                          #-}
{-# LANGUAGE ScopedTypeVariables                      #-}
{-# LANGUAGE TupleSections                            #-}
{-# LANGUAGE TypeApplications                         #-}
{-# LANGUAGE TypeOperators                            #-}
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
import           Data.Primitive.MutVar
import           Data.Proxy
import           Data.Time
import           GHC.TypeNats
import           Numeric.Natural
import           Numeric.Opto
import           Options.Applicative
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import           Text.Printf
import qualified Data.Conduit.Combinators       as C
import qualified System.Random.MWC              as MWC

data Mode = CSimulate (Maybe Int)
          | CLearn Model
  deriving Show

data Model = MARMA
           | MFCRNN
  deriving Show

data Options = O { oMode  :: Mode
                 , oP     :: Natural
                 , oQ     :: Natural
                 , oNoise :: Double
                 }
  deriving Show

armaSim :: (KnownNat p, KnownNat q) => ARMA p q
armaSim = ARMA { _armaGenPhi   = \g i ->
                    (/ (fromIntegral i + 5)) <$> genContVar (normalDistr 0 2) g
               , _armaGenTheta = \g i ->
                    (/ (fromIntegral i + 5)) <$> genContVar (normalDistr 0 2) g
               , _armaGenConst = genContVar $ normalDistr 0 0.2
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
    let armaSim'  = armaSim @p @q

    case oMode of
      CSimulate lim -> do
        runConduit $ genSim armaSim' oNoise g
                  .| maybe (C.map id) C.take lim
                  .| C.mapM_ print
                  .| C.sinkNull

      CLearn MARMA -> do
        let model = armaUnroll armaSim'
        p0 <- fromJ_ $ initParam model g

        let report n b = do
              liftIO $ printf "(Batch %d)\n" (b :: Int)
              t0 <- liftIO getCurrentTime
              C.drop (n - 1)
              mp <- mapM (liftIO . evaluate . force) =<< await
              t1 <- liftIO getCurrentTime
              case mp of
                Nothing -> liftIO $ putStrLn "Done!"
                Just p  -> do
                  chnk <- lift . state $ (,[])
                  liftIO $ do
                    printf "Trained on %d points in %s.\n"
                      (length chnk)
                      (show (t1 `diffUTCTime` t0))
                    let e = norm_2 (p0 - p)
                    printf "Error: %0.4f\n" e
                  report n (b + 1)

        flip evalStateT []
            . runConduit
            $ genSim armaSim' oNoise g
           .| consecutivesN
           .| skipSampling 0.02 g
           .| C.iterM (modify . (:))
           .| runOptoConduit_
                (RO' Nothing Nothing)
                p0
                (adam @_ @(MutVar _ _) def
                   (learnGrad (sumLossDecay 0.1 squaredError) model)
                )
           .| report 5000 0
           .| C.sinkNull
      CLearn MFCRNN -> error "fcrnn: unimplemented."

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
  where
    parseSim :: Parser Mode
    parseSim = CSimulate <$> optional (option auto
                                          ( short 'n'
                                         <> help "Number of items to generate (infinite, if none given)"
                                         <> metavar "INT"
                                          )
                                      )
    parseLearn :: Parser Mode
    parseLearn = CLearn <$> subparser
        ( command "arma"  (info (pure MARMA ) (progDesc "Learn ARMA model"))
       <> command "fcrnn" (info (pure MFCRNN) (progDesc "Learn Fully Connected RNN model"))
        )
