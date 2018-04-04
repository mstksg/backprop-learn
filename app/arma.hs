{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

import           Backprop.Learn
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
import           Data.Time
import           Numeric.Opto
import           Statistics.Distribution
import           Statistics.Distribution.Normal
import           Text.Printf
import qualified Data.Conduit.Combinators       as C
import qualified Data.Vector                    as V
import qualified System.Random.MWC              as MWC

armaSim :: ARMA 4 4
armaSim = ARMA { _armaGenPhi   = \g i ->
                    (/ (fromIntegral i + 5)) <$> genContVar (normalDistr 0 2) g
               , _armaGenTheta = \g i ->
                    (/ (fromIntegral i + 5)) <$> genContVar (normalDistr 0 2) g
               , _armaGenConst = genContVar $ normalDistr 0 0.2
               , _armaGenYHist = genContVar $ normalDistr 0 0.2
               , _armaGenEHist = genContVar $ normalDistr 0 0.2
               }

genSim
    :: forall m i. PrimMonad m
    => MWC.Gen (PrimState m)
    -> ConduitT i Double m ()
genSim g = do
    p  <- fromJ_ $ initParam noisySim g
    s0 <- fromJ_ $ initState noisySim g
    void . foldr (>=>) pure (repeat (go p)) $ (0, J_I s0)
  where
    noisySim = armaSim :.~ injectNoise (normalDistr 0 0.05)
    go  :: ARMAp 4 4
        -> (Double, Mayb I ('Just (ARMAs 4 4)))
        -> ConduitT i Double m (Double, Mayb I ('Just (ARMAs 4 4)))
    go p (y, s) = do
      ys@(y', _) <- lift $ runLearnStoch_ noisySim g (J_I p) y s
      ys <$ yield y'

main :: IO ()
main = MWC.withSystemRandom @IO $ \g -> do
    p0 <- fromJ_ $ initParam armaLearn g

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
        $ genSim g
       .| consecutivesN @V.Vector @4
       .| skipSampling 0.02 g
       .| C.iterM (modify . (:))
       .| runOptoConduit_
            (RO' Nothing Nothing)
            p0
            (adam @_ @(MutVar _ _) def
               (learnGrad (sumLossDecay 0.1 squaredError) armaLearn)
            )
       .| report 5000 0
       .| C.sinkNull
  where
    armaLearn :: ARMAUnroll 4 4
    armaLearn = armaUnroll armaSim
