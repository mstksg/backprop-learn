{-# LANGUAGE OverloadedStrings #-}

import           Reflex.Dom

main :: IO ()
main = mainWidget $ el "div" $ do
    t <- textInput def
    dynText $ _textInput_value t
