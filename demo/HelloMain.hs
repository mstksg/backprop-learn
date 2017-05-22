{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE JavaScriptFFI #-}

import Control.Monad.IO.Class (MonadIO(..))
import Control.Concurrent.MVar (takeMVar, putMVar, newEmptyMVar)

import GHCJS.DOM (syncPoint, currentDocumentUnchecked)
import GHCJS.DOM.Types
       -- (Element(..), HTMLParagraphElement(..),
       --  HTMLSpanElement(..), uncheckedCastTo, JSM)
import GHCJS.DOM.Document (getBodyUnsafe, createElement, createTextNode)
import GHCJS.DOM.Element (setInnerHTML, setAttribute)
import GHCJS.DOM.HTMLCanvasElement
import GHCJS.DOM.CanvasRenderingContext2D
import GHCJS.DOM.ImageData
import GHCJS.DOM.Node (appendChild)
import GHCJS.DOM.EventM (on, mouseClientXY)
import Language.Javascript.JSaddle.WebKitGTK (run)
import GHCJS.DOM.GlobalEventHandlers (click)

import           JavaScript.Array
import           GHCJS.Types

main :: IO ()
main = run helloMain

helloMain :: JSM ()
helloMain = do
    doc <- currentDocumentUnchecked
    body <- getBodyUnsafe doc
    canvas <- uncheckedCastTo HTMLCanvasElement <$> createElement doc "canvas"
    setAttribute canvas "height" "500"
    setAttribute canvas "width" "500"
    Just ctx' <- getContext canvas "2d" ([] :: [JSString])
    let ctx = CanvasRenderingContext2D (unRenderingContext ctx')
    
    carr <- js_newUint8ClampedArray $
       fromList (fmap (pToJSVal @Int . (`mod` 256)) [1 .. (500 * 500 * 4)])

    imdat <- newImageData carr 500 (Just 500)

    _ <- appendChild body canvas

    putImageData ctx imdat 0 0

    return ()

foreign import javascript unsafe
    "new window[\"Uint8ClampedArray\"]($1)" js_newUint8ClampedArray ::
      JSArray -> IO Uint8ClampedArray


    -- setInnerHTML body (Just "<h1>Kia ora (Hi)</h1>")
    -- _ <- on doc click $ do
    --     (x, y) <- mouseClientXY
    --     newParagraph <- uncheckedCastTo HTMLParagraphElement <$> createElement doc "p"
    --     text <- createTextNode doc $ "Click " ++ show (x, y)
    --     _ <- appendChild newParagraph text
    --     _ <- appendChild body newParagraph
    --     return ()

    -- -- Make an exit button
    -- exitMVar <- liftIO newEmptyMVar
    -- exit <- uncheckedCastTo HTMLSpanElement <$> createElement doc "span"
    -- text <- createTextNode doc "Click here to exit"
    -- _ <- appendChild exit text
    -- _ <- appendChild body exit
    -- _ <- on exit click $ liftIO $ putMVar exitMVar ()

    -- -- Force all all the lazy JSaddle evaluation to be executed
    -- syncPoint

    -- -- In GHC compiled version the WebSocket connection will end when this
    -- -- thread ends.  So we will wait until the user clicks exit.
    -- liftIO $ takeMVar exitMVar
    -- setInnerHTML body (Just "<h1>Ka kite ano (See you later)</h1>")
    -- return ()
