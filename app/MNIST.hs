{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

import           Control.DeepSeq
import           Control.Exception
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Maybe
import           Data.Bitraversable
import           Data.Finite
import           Data.Foldable
import           Data.IDX
import           Data.Traversable
import           Data.Tuple
import           Learn.Neural.Layer
import           Learn.Neural.Layer.FullyConnected
import           Learn.Neural.Layer.Mapping
import           Learn.Neural.Network
import           Numeric.BLAS
import           Numeric.BLAS.HMatrix
import           Numeric.LinearAlgebra.Static
import           Numeric.Tensor
import qualified Data.Vector.Generic               as VG
import qualified Data.Vector.Unboxed               as VU
import qualified System.Random.MWC                 as MWC

loadMNIST
    :: FilePath
    -> FilePath
    -> IO (Maybe [(HM (BV 784), HM (BV 10))])
loadMNIST fpI fpL = runMaybeT $ do
    i <- MaybeT          $ decodeIDXFile       fpI
    l <- MaybeT          $ decodeIDXLabelsFile fpL
    d <- MaybeT . return $ labeledIntData l i
    r <- MaybeT . return $ for d (bitraverse mkImage mkLabel . swap)
    liftIO . evaluate $ force r
  where
    mkImage :: VU.Vector Int -> Maybe (HM (BV 784))
    mkImage = fmap HM . create . VG.convert . VG.map (\i -> fromIntegral i / 255)
    mkLabel :: Int -> Maybe (HM (BV 10))
    mkLabel = fmap (oneHot . BVIx) . packFinite . fromIntegral

main :: IO ()
main = MWC.withSystemRandom $ \g -> do
    Just test  <- loadMNIST "data/t10k-images-idx3-ubyte"  "data/t10k-labels-idx1-ubyte"
    putStrLn "Loaded data."
    net0 :: Network 'FeedForward HM ( BV 784 :~ FullyConnected )
                                   '[ BV 300 :~ LogitMap
                                    , BV 300 :~ FullyConnected
                                    , BV 100 :~ LogitMap
                                    , BV 100 :~ FullyConnected
                                    , BV 10  :~ LogitMap
                                    ]
                                    (BV 10) <- initDefNet g
    putStrLn "hi"
    -- forM_ test $ \(_, i) ->
    --   print $ iamax i
