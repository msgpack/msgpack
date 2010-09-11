{-# Language OverloadedStrings #-}

import Control.Monad.IO.Class
import qualified Data.ByteString as B
import Data.MessagePack

main = do
  sb <- return $ packToString $ do
    put [1,2,3::Int]
    put (3.14 :: Double)
    put ("Hoge" :: B.ByteString)
  
  print sb
  
  r <- unpackFromString sb $ do
    arr <- get
    dbl <- get
    str <- get
    return (arr :: [Int], dbl :: Double, str :: B.ByteString)
  
  print r
