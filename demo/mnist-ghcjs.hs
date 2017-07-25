{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE JavaScriptFFI         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ViewPatterns          #-}

-- import           GHCJS.DOM
-- import Control.Applicative        ((<*>), (<$>))
-- import Data.Text                  (pack, unpack, Text)
-- import Reflex.Dom
-- import Safe                       (readMay)
-- import qualified Data.Map         as Map
-- import           Data.Foldable
-- import           Data.List.Split
-- import           GHCJS.DOM.Element
-- import qualified Data.Vector                     as V
-- import qualified System.Random.MWC.Distributions as MWC

import           Codec.Picture
import           Control.Concurrent
import           Control.DeepSeq
import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Monoid
import           Data.Singletons
import           Data.Time.Clock
import           Data.Type.Product hiding           (toList)
import           Data.Word
import           GHCJS.DOM.CanvasRenderingContext2D
import           GHCJS.DOM.HTMLCanvasElement
import           GHCJS.DOM.ImageData
import           GHCJS.Types
import           Learn.Neural
import           Lens.Micro
import           Numeric.BLAS.NVector
import           Reflex
import           Reflex.Dom
import           Text.Printf
import qualified Data.Text                          as T
import qualified GHCJS.DOM.Types                    as JS
import qualified JavaScript.Array                   as JS
import qualified System.Random.MWC                  as MWC

sampleSize :: Int
sampleSize = 15

canvScale :: Int
canvScale = 20

main :: IO ()
main = MWC.withSystemRandom $ \g -> mainWidget $ do
    tchan <- liftIO $ do
        tc <- newChan
        tc <$ forkIO (trainThread tc g)
    (epochEvt, funcEvt) <- splitE <$> chainDyn tchan
    let imgEvt :: Event (SpiderTimeline Global) (Image PixelRGBA8)
        imgEvt = ffor funcEvt $ \f ->
            let mkPx px py =
                    let x = fromIntegral px / fromIntegral sampleSize
                        y = fromIntegral py / fromIntegral sampleSize
                        z = round . min 255 . max 0 $
                              f x y * 255
                    in  PixelRGBA8 z z z 255
                !im0 = generateImage mkPx sampleSize sampleSize
            in  scaleImg canvScale im0
        img0 = generateImage (\_ _ -> PixelRGBA8 0 0 0 255)
                 (sampleSize * canvScale)
                 (sampleSize * canvScale)
    imgDyn <- holdDyn img0 imgEvt

    dynCanvas imgDyn (sampleSize * canvScale) (sampleSize * canvScale)
    dynText =<< holdDyn "..." (T.pack . show <$> epochEvt)
    return ()

scaleImg :: Pixel p => Int -> Image p -> Image p
scaleImg s i0 = generateImage f (imageWidth i0 * s) (imageHeight i0 * s)
  where
    f i j = pixelAt i0 (i `div` s) (j `div` s)

chainDyn
    :: (TriggerEvent t m, MonadIO m)
    => Chan a
    -> m (Event t a)
chainDyn c = do
    (evt, trig) <- newTriggerEvent
    _ <- liftIO . forkIO . forever $ do
      e <- readChan c
      trig e
    return evt

trainThread :: Chan (Int, Double -> Double -> Double) -> MWC.GenIO -> IO ()
trainThread c g = do
    net0 :: Network 'FeedForward NV ( '[2] :~ FullyConnected )
                                   '[ '[8] :~ LogitMap
                                    , '[8] :~ FullyConnected
                                    , '[4] :~ LogitMap
                                    , '[4] :~ FullyConnected
                                    , '[1] :~ LogitMap
                                    ]
                                    '[1] <- initDefNet g
    flip evalStateT net0 . forM_ [1..] $ \e -> StateT $ \n0 -> do
      printf "[Epoch %d]\n" (e :: Int)

      t0t <- getCurrentTime
      train' <- replicateM batch $ do
          x <- MWC.uniformR (0, 1) g
          y <- MWC.uniformR (0, 1) g
          let xy :: NV '[2]
              xy = twoItems sing x y

          return (xy, treshape sing . fromScalar $ func x y)
      train <- evaluate $ force train'
      t1t <- getCurrentTime
      printf "Generated %d points in %s.\n" batch (show (t1t `diffUTCTime` t0t))

      t0 <- getCurrentTime
      n' <- evaluate $ optimizeList_ (bimap only_ only_ <$> train) n0
                                     -- (sgdOptimizer 0.1 netOpPure crossEntropy)
                                     (adamOptimizer def netOpPure squaredError)
      t1 <- getCurrentTime
      printf "Trained on %d points in %s.\n" (length train) (show (t1 `diffUTCTime` t0))

      -- writeChan c $ \x y ->
      --   sqrt $ (x - 0.5)**2 + (y - 0.5)**2
      -- writeChan c $ \x y ->
      --   toScalar . treshape sing $ func x y
      writeChan c . (e,) $ \x y ->
        let xy = twoItems sing x y
        in  toScalar . treshape sing $ runNetPure n' xy

      -- forM_ ((,) <$> [1..sampleSize] <*> [1..sampleSize]) $ \(px, py) -> do
      --   let x = fromIntegral px / fromIntegral sampleSize
      --       y = fromIntegral py / fromIntegral sampleSize
      --       xy = twoItems sing x y
      --       z = toScalar . treshape sing $ runNetPure n' xy
      --       z' = toScalar . treshape sing $ func x y
      --   printf "(%.2f,%.2f): %.4f / %.4f\n" x y z z'

      return ((), n')
  where
    batch :: Int
    batch = 500
    func x y | y < x     = 1
             | otherwise = 0

    -- func x y | (x < (1/3)) || (x > (2/3)) = 1
    --          | otherwise = 0
    -- func :: Double -> Double -> Double
    -- func x y | r1 < (1/6) = 1
    --          | r2 < (1/6) = 1
    --          | otherwise  = 0
    --   where
    --     r1 = sqrt $ (x-0.25)**2 + (y-0.25)**2
    --     r2 = sqrt $ (x-0.75)**2 + (y-0.75)**2

dynCanvas
    :: (PerformEvent t m, DomBuilder t m, MonadIO (Performable m), RawElement (DomBuilderSpace m) ~ JS.Element)
    => Dynamic t (Image PixelRGBA8)
    -> Int
    -> Int
    -> m ()
dynCanvas i h w = do
    (canv, ()) <- elAttr' "canvas" ("height" =: T.pack (show h) <> "width" =: T.pack (show w)) (return ())
    let canvElem = JS.uncheckedCastTo JS.HTMLCanvasElement $ _element_raw canv
    performEvent_ . ffor (updated i) $ \img -> liftIO $ do
      t0 <- getCurrentTime
      Just ctx' <- getContext canvElem ("2d" :: JSString) ([] :: [JSString])
      let ctx    = JS.CanvasRenderingContext2D (JS.unRenderingContext ctx')
          pixels = toListOf (imagePixels . prgba8 . to JS.pToJSVal) img
      carr  <- js_newUint8ClampedArray $ JS.fromList (map JS.pToJSVal pixels)
      imdat <- newImageData carr
                 (fromIntegral (imageHeight img))
                 (Just (fromIntegral (imageWidth img)))
      putImageData ctx imdat 0 0
      t1 <- getCurrentTime
      printf "Drew image in %s.\n" (show (t1 `diffUTCTime` t0))
  where
    prgba8 :: Traversal' PixelRGBA8 Word8
    prgba8 f (PixelRGBA8 r g b a) = PixelRGBA8 <$> f r <*> f g <*> f b <*> f a

foreign import javascript unsafe
    "new window[\"Uint8ClampedArray\"]($1)" js_newUint8ClampedArray ::
      JS.JSArray -> IO JS.Uint8ClampedArray

