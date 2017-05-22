#!/usr/bin/env stack
-- stack --install-ghc runghc --package shake

{-# LANGUAGE ViewPatterns #-}

import           Development.Shake
import           Development.Shake.FilePath
import           System.Directory

opts = shakeOptions { shakeFiles     = ".shake"
                    , shakeVersion   = "1.0"
                    , shakeVerbosity = Normal
                    , shakeThreads   = 0
                    }

main :: IO ()
main = getDirectoryFilesIO "demo" ["/*.lhs", "/*.hs"] >>= \allDemos ->
       getDirectoryFilesIO "src"  ["//*.hs"]          >>= \allSrc ->
         shakeArgs opts $ do

    want ["all"]

    "all" ~>
      -- need ["haddocks", "gentags", "install", "exe", "js"]
      need ["haddocks", "gentags", "install", "js"]

    "exe" ~>
      need (map (\f -> "demo-exe" </> dropExtension f) allDemos)

    "js" ~>
      need (map (\f -> "demo-js" </> (f -<.> "jsexe") </> "all.js") allDemos)

    "haddocks" ~> do
      need (("src" </>) <$> allSrc)
      cmd "jle-git-haddocks"

    "install" ~> do
      need $ ("src" </>) <$> allSrc
      cmd "stack install"

    "install-ghcjs" ~> do
      need $ ("src" </>) <$> allSrc
      cmd "stack install --stack-yaml stack-ghcjs.yaml"

    "gentags" ~>
      need ["tags", "TAGS"]

    "demo-exe/*" %> \f -> do
      need ["install"]
      [src] <- getDirectoryFiles "demo" $ (takeFileName f <.>) <$> ["hs","lhs"]
      liftIO $ do
        createDirectoryIfMissing True "demo-exe"
        createDirectoryIfMissing True ".build"
      removeFilesAfter "demo" ["/*.o"]
      cmd "stack exec" "--package backprop-learn"
                       "--"
                       "ghc"
                       ("demo" </> src)
                       "-o" f
                       "-hidir" ".build"
                       "-threaded"
                       "-rtsopts"
                       "-with-rtsopts=-N"
                       "-Wall"
                       "-O2"

    "demo-js/*.jsexe/all.js" %> \(takeDirectory -> f) -> do
      need ["install-ghcjs"]
      [src] <- getDirectoryFiles "demo" $ (takeFileName f -<.>) <$> ["hs","lhs"]
      liftIO $ do
        -- createDirectoryIfMissing True (takeDirectory f)
        createDirectoryIfMissing True "demo-js"
        createDirectoryIfMissing True ".build"
      removeFilesAfter "demo" ["/*.o","/*.js_o"]
      cmd "stack exec" "--package backprop-learn"
                       "--package reflex-dom"
                       "--package JuicyPixels"
                       -- "--package jsaddle-wkwebview"
                       "--package jsaddle-webkit2gtk"
                       "--stack-yaml stack-ghcjs.yaml"
                       "--"
                       "ghcjs"
                       ("demo" </> src)
                       "-o" f
                       "-hidir" ".build"
                       "-threaded"
                       "-rtsopts"
                       "-with-rtsopts=-N"
                       "-Wall"
                       "-O2"

    ["tags","TAGS"] &%> \_ -> do
      need (("src" </>) <$> allSrc)
      cmd "hasktags" "src/"

    "clean" ~> do
      unit $ cmd "stack clean"
      removeFilesAfter ".shake" ["//*"]
      removeFilesAfter ".build" ["//*"]
      removeFilesAfter "demo-exe" ["//*"]

