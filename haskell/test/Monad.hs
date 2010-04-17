import Control.Monad.Trans
import Data.MessagePack

main = do
  sb <- packToString $ do
    put [1,2,3::Int]
    put (3.14 :: Double)
    put "Hoge"
  
  print sb
  
  unpackFromString sb $ do
    arr <- get
    dbl <- get
    str <- get
    liftIO $ print (arr :: [Int], dbl :: Double, str :: String)
