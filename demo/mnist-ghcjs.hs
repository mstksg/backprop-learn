{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE JavaScriptFFI         #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
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

import           Codec.Picture
import           Control.Concurrent
import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Foldable
import           Data.List.Split
import           Data.Monoid
import           Data.Singletons
import           Data.Time.Clock
import           Data.Type.Product hiding           (toList)
import           Data.Word
import           GHCJS.DOM.CanvasRenderingContext2D
import           GHCJS.DOM.Element
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
import qualified Data.Vector                        as V
import qualified GHCJS.DOM.Types                    as JS
import qualified JavaScript.Array                   as JS
import qualified System.Random.MWC                  as MWC
import qualified System.Random.MWC.Distributions    as MWC

main :: IO ()
main = MWC.withSystemRandom $ \g -> mainWidget $ do
    tchan <- liftIO $ do
        tc <- newChan
        tc <$ forkIO (trainThread tc g)
    funcEvt <- chainDyn tchan
    let imgEvt :: Event _ (Image PixelRGBA8)
        !imgEvt = ffor funcEvt $ \f ->
            let mkPx px py =
                    let x = fromIntegral px / 50
                        y = fromIntegral py / 50
                        z = round . min 255 . max 0 $
                              f x y * 255
                    in  PixelRGBA8 z z z 255
            in  generateImage mkPx 50 50
        img0 = generateImage (\_ _ -> PixelRGBA8 0 0 0 255) 50 50
    imgDyn <- holdDyn img0 imgEvt

    dynCanvas imgDyn 50 50
    return ()

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

trainThread :: Chan (Double -> Double -> Double) -> MWC.GenIO -> IO ()
trainThread c g = do
    net0 :: Network 'FeedForward NV ( '[2]  :~ FullyConnected )
                                   '[ '[8]  :~ LogitMap
                                    , '[8]  :~ FullyConnected
                                    , '[1]  :~ LogitMap
                                    ]
                                    '[1] <- initDefNet g
    flip evalStateT net0 . forM_ [1..] $ \e -> StateT $ \n0 -> do
      train <- replicateM 1000 $ do
          x <- MWC.uniformR (0, 1) g
          y <- MWC.uniformR (0, 1) g
          let xy :: NV '[2]
              Just xy = fromList sing [x,y]

          return (xy, func x y)

      printf "[Epoch %d]\n" (e :: Int)

      t0 <- getCurrentTime
      n' <- evaluate $ optimizeList_ (bimap only_ only_ <$> train) n0
                                     -- (sgdOptimizer 0.1 netOpPure crossEntropy)
                                     (adamOptimizer def netOpPure crossEntropy)
      t1 <- getCurrentTime
      printf "Trained on %d points in %s.\n" (length train) (show (t1 `diffUTCTime` t0))

      -- writeChan c $ \x y ->
      --   sqrt $ (x - 0.5)**2 + (y - 0.5)**2
      -- writeChan c $ \x y ->
      --   toScalar . treshape sing $ func x y
      writeChan c $ \x y ->
        let Just xy = fromList sing [x,y]
        in  toScalar . treshape sing $ runNetPure n' xy

      return ((), n')
  where
    func :: Double -> Double -> NV '[1]
    func x y | r < 0.33   = 1
             | otherwise  = 0
      where
        r = sqrt $ (x-0.5)**2 + (y-0.5)**2

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
      Just ctx' <- getContext canvElem ("2d" :: JSString) ([] :: [JSString])
      let ctx    = JS.CanvasRenderingContext2D (JS.unRenderingContext ctx')
          pixels = toListOf (imagePixels . prgba8 . to JS.pToJSVal) img
      carr  <- js_newUint8ClampedArray $ JS.fromList (map JS.pToJSVal pixels)
      imdat <- newImageData carr
                 (fromIntegral (imageHeight img))
                 (Just (fromIntegral (imageWidth img)))
      putImageData ctx imdat 0 0
  where
    prgba8 :: Traversal' PixelRGBA8 Word8
    prgba8 f (PixelRGBA8 r g b a) = PixelRGBA8 <$> f r <*> f g <*> f b <*> f a

foreign import javascript unsafe
    "new window[\"Uint8ClampedArray\"]($1)" js_newUint8ClampedArray ::
      JS.JSArray -> IO JS.Uint8ClampedArray

