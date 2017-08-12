{-# LANGUAGE Arrows                 #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE ExplicitNamespaces     #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TupleSections          #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

-- import           Learn.Neural.Layer.Recurrent.LSTM
-- import qualified Control.Monad.Trans.Resource             as R
-- import qualified Data.Conduit.Audio                       as A
-- import qualified Data.Conduit.Audio.Sndfile               as A
-- import qualified Data.Conduit.List                        as C
-- import qualified Data.Vector.Storable                     as VS
-- import qualified Sound.File.Sndfile                       as A
import           Control.Arrow                               ((|||))
import           Control.Auto
import           Control.Category
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Reader
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Complex
import           Data.Foldable
import           Data.Kind hiding                            (type (*))
import           Data.List
import           Data.Maybe
import           Data.Profunctor
import           Data.Singletons
import           Data.Time.Clock
import           Data.Type.Combinator
import           Data.Type.Product hiding                    (toList)
import           Data.Type.Vector
import           Data.Word
import           GHC.TypeLits
import           Learn.Neural
import           Learn.Neural.Layer.Recurrent.FullyConnected
import           Numeric.BLAS.HMatrix
import           Numeric.Backprop.Op hiding                  (head')
import           Prelude hiding                              (id, (.))
import           Text.Printf
import           Type.Class.Known
import qualified Codec.Wav                                   as HC
import qualified Data.Array.Unboxed                          as UA
import qualified Data.Audio                                  as HC
import qualified Data.Type.Nat                               as TCN
import qualified Data.Vector.Sized                           as SV
import qualified System.Random.MWC                           as MWC
import qualified System.Random.MWC.Distributions             as MWC
import qualified Type.Family.Nat                             as TCN

type HasTime = Reader Double

sineSig :: Double -> Auto HasTime Double Double
sineSig θ = flip mkStateM_ (cis θ) $ \ω r -> reader $ \dt ->
              let r' = r * cis (ω * dt)
              in  (realPart r', r')

netSig
    :: (BLAS b, Num (b i), Num (b o))
    => SomeNet r b i o
    -> Auto m (b i) (b o)
netSig (SomeNet _ n0) = mkState_ (flip runNet) n0

-- | Match [-1,1] logarithmically to the given range
pitch
    :: Double       -- ^ minimum frequency range (Hz)
    -> Double       -- ^ maximum frequency range (Hz
    -> Double       -- ^ [-1, 1]
    -> Double
pitch l h = go
  where
    lnL = log l
    lnRange = log h - lnL
    go x = exp ((x / 2 + 0.5) * lnRange + lnL)

pitch' :: Double -> Double
pitch' = pitch (middleC / 2) (middleC * 2)
  where
    middleC = 440 / (2**(3/4))

pitchSig :: Double -> Auto HasTime Double Double
pitchSig = lmap ((* (2 * pi)) . pitch') . sineSig

sample
    :: KnownNat n
    => Double           -- ^ Sampling rate (Hz)
    -> Double           -- ^ How quickly frequency moves (notes per second)
    -> MWC.GenIO
    -> IO (SV.Vector n ((Double, Double), Double))
sample r v g = do
    f0 <- MWC.uniformR (-1, 1) g
    θ0 <- MWC.uniformR (0, pi * 2) g
    evalStateT (SV.replicateM (StateT go)) (f0, θ0, pitchSig θ0)
  where
    dt = 1/r
    σ = v / sqrt r / 12
    go  :: (Double, Double, Auto HasTime Double Double)
        -> IO (((Double, Double), Double), (Double, Double, Auto HasTime Double Double))
    go (f0, x, sig0) = do
      f1 <- max (-1) . min 1 . (+ f0) <$> MWC.normal 0 σ g
      let (y, sig1) = runReader (stepAuto sig0 f1) dt
      return (((f1, x), y), (f1, y, sig1))

vecVec :: Known TCN.Nat (NatNat n) => SV.Vector n a -> Vec (NatNat n) a
vecVec = evalState (sequence (vgen_ (I . const (state go)))) . toList
  where
    go []     = undefined
    go (x:xs) = (x, xs)

type family NatNat (n :: Nat) = (m :: TCN.N) where
    NatNat 0 = 'TCN.Z
    NatNat n = 'TCN.S (NatNat (n - 1))

main :: IO ()
main = MWC.withSystemRandom @IO $ \g -> do

    let opt0 = batching $ adamOptimizer def (netOpRecurrent_ known)
                            (sumLoss squaredError known)
    net0 :: Network 'Recurrent HM ( '[2]  :~ FullyConnectedR' 'MF_Logit )
                                 '[ '[10] :~ ReLUMap
                                  , '[10] :~ FullyConnectedR' 'MF_Logit
                                  , '[10] :~ ReLUMap
                                  , '[10] :~ FullyConnected
                                  ]
                                  '[1] <- initDefNet g

    flip evalStateT (net0, opt0) . forM_ [1..] $ \(e :: Int) -> StateT $ \(n0, o0) -> do
      printf "Epoch %d\n" e

      samps <- replicateM batch $ do
        v <- MWC.uniformR (0, 4) g
        unzipV . vecVec . fmap (bimap (uncurry twoItems) oneItem) <$>
          sample @50 11000 v g

      t0 <- getCurrentTime
      (n', o') <- bitraverse evaluate evaluate
        $ optimizeListBatches (bimap vecToProd vecToProd <$> samps) n0 o0 25
      t1 <- getCurrentTime
      printf "Trained on %d points in %s.\n" batch (show (t1 `diffUTCTime` t0))

      let prime ω0 = snd . flip runReader (1/11000) . flip (stepAutoN 11000) (ω0, False) $ proc (ω, fb) -> do
            rec o <- (delay 0 . pitchSig 0) ||| id -< if fb
                        then Right . toScalar . treshape sing $ r
                        else Left ω
                r <- delay_ 0 . netSig (someNet n') -< twoItems ω o
                    -- if fb then toScalar . treshape sing $ r
                    --       else o
            id -< r
          genNet ns ωs = flip runReader (1/11000) $ streamAuto ns (map (, True) ωs)
          testMiddleC   = genNet (prime 0)    (replicate 22000 0)
          testAscending = genNet (prime (-1)) [fromIntegral i / 11000 - 1 | i <- [1 .. 22000]]
      HC.exportFile "test-middlec.wav"   $ foldAudio 11000 (concatMap tlist testMiddleC)
      HC.exportFile "test-ascending.wav" $ foldAudio 11000 (concatMap tlist testAscending)
      writeFile "test-middlec.dat"   $ unlines (concatMap (map show . tlist) testMiddleC)
      writeFile "test-ascending.dat" $ unlines (concatMap (map show . tlist) testAscending)

      return ((), (n', o'))

  where
    batch :: Int
    batch = 1000

oneItem :: Double -> HM '[1]
oneItem = treshape sing . fromScalar
twoItems :: Double -> Double -> HM '[2]
twoItems x y = fromJust $ fromList sing [x, y]


    -- samp <- sample @1320000 44000 1 g
    -- print $ length samp
    -- HC.exportFile "sine.wav" $ foldAudio 44000 samp
    -- mapM_ print samp
    -- let testSine = take 100000 . flip unfoldr (sineSig 0) $ \sig -> Just (runSignal sig (1/44000) (440 * (2 * pi)))
    -- mapM_ (print . round @_ @Word8 . max 0 . min 255 . (*255) . (/2) . (+1)) testSine
    -- HC.exportFile "sine.wav" $ foldAudio 44000 testSine
    -- let fmt = A.Format A.HeaderFormatWav A.SampleFormatDouble A.EndianCpu
    -- R.runResourceT $ A.sinkSnd "sine.wav" fmt (foldAudio 10000 samp)
    -- mapM_ print . take 100 . flip unfoldr (sineSig 0) $ \sig -> Just (runSignal sig 0.1 1)
    -- mapM_ print $ map (\x -> middleC * ((2**(1/12)) ** fromIntegral x)) [-12..12]
    -- putStrLn ""
    -- mapM_ print $ map (\x -> pitch (middleC / 2) (middleC * 2) (fromIntegral x / 20)) [0..20]
    -- mapM_ print $ map (\x -> pitch' (fromIntegral x / 10 - 1)) [0..20]
    -- putStrLn "hi"


-- | Cheap signals

-- data Tup2 a b = Tup2 !a !b

-- data Sig :: Type -> Type -> Type where
--     Sig :: !s -> (Double -> a -> s -> (b, s)) -> Sig a b

-- deriving instance Functor (Sig r)
-- instance Applicative (Sig r) where
--     pure x = Sig () (\_ _ () -> (x, ()))
--     Sig sF fF <*> Sig sX fX = Sig (Tup2 sF sX) $ \dt i (Tup2 sF0 sX0) ->
--       let (oF, sF1) = fF dt i sF0
--           (oX, sX1) = fX dt i sX0
--       in  (oF oX, Tup2 sF1 sX1)
-- instance Profunctor Sig where
--     dimap f g (Sig s h) = Sig s $ \dt x s0 ->
--       let (y, s1) = h dt (f x) s0
--       in  (g y, s1)
-- instance Category Sig where
--     id = Sig () (\_ x () -> (x, ()))
--     -- Sig


-- runSignal :: Sig a b -> Double -> a -> (b, Sig a b)
-- runSignal (Sig s0 f) dt x = let (y, s1) = f dt x s0
--                             in  (y, Sig s1 f)

-- scanSignal :: Sig a b -> [(Double, a)] -> ([b], Sig a b)
-- scanSignal sig0 []          = ([], sig0)
-- scanSignal sig0 ((dt,x):xs) = let (y , sig1) = runSignal  sig0 dt x
--                                   (ys, sig2) = scanSignal sig1 xs
--                               in  (y:ys, sig2)

foldAudio :: Foldable f => Int -> f Double -> HC.Audio Word8
foldAudio r xs = HC.Audio r 1 (UA.listArray (0, length xs - 1) (w <$> toList xs))
  where
    w = round . max 0 . min 255 . (*255) . (/2) . (+1)

vecToProd
    :: VecT n f a
    -> Prod f (Replicate n a)
vecToProd = \case
    ØV      -> Ø
    x :* xs -> x :< vecToProd xs

unzipV :: Vec n (a, b) -> (Vec n a, Vec n b)
unzipV = \case
    ØV -> (ØV, ØV)
    I (x, y) :* xys -> bimap (I x :*) (I y :*) $ unzipV xys
